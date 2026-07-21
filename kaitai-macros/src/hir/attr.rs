use crate::{
    de,
    hir::{doc::Doc, meta::Endianness},
    util::sc_to_ucc,
};

use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens};
use std::collections::HashMap;

pub use crate::de::data::IntegerValue;

/// Extra information about a `_root.X.Y` dependency discovered in a sub-type's
/// switch-on expressions. Used by the parent type to generate `new_with_root`
/// calls instead of the standard `KaitaiStruct::new` calls.
#[derive(Clone, Debug)]
pub struct RootParam {
    /// The full `_root.…` path string as it appears in the YAML switch-on.
    pub path: String,
    /// Sanitised parameter identifier: `_root.flags.timestamps_64bit` →
    /// `root_flags_timestamps_64bit`.
    pub param_ident: Ident,
    /// Rust type of the parameter, derived from the switch case patterns
    /// (e.g. `bool` when cases are `true`/`false`, a widened int otherwise).
    pub param_ty: TokenStream,
    /// Expression that produces the value in the *parent* type's `new()` scope
    /// (e.g. `flags.timestamps_64bit`).
    pub accessor: TokenStream,
}

#[derive(Clone, Debug)]
pub struct Attributes(pub(crate) Vec<Attribute>);

impl TryFrom<(Option<de::meta::MetaDoc>, Vec<de::attr::Attr>)> for Attributes {
    type Error = ();

    fn try_from(
        (meta_doc, attrs): (Option<de::meta::MetaDoc>, Vec<de::attr::Attr>),
    ) -> Result<Self, Self::Error> {
        Ok(Self(
            attrs
                .into_iter()
                .map(|a| (meta_doc.clone(), a).try_into())
                .collect::<Result<Vec<_>, _>>()?,
        ))
    }
}

impl Attributes {
    pub fn field_definitions(&self) -> impl Iterator<Item = TokenStream> + '_ {
        self.0
            .iter()
            .filter(|a| a.is_stored())
            .map(|a| a.field_definition())
    }

    /// Returns `true` if any attribute in the sequence is a bit-width field.
    pub fn has_bit_fields(&self) -> bool {
        self.0.iter().any(|a| a.is_bit_field())
    }

    /// Collects all `_root.X.Y` switch-on references in this attribute list.
    /// Deduplicates by path so each unique dependency appears only once.
    pub fn root_refs(&self) -> Vec<RootParam> {
        let mut seen = std::collections::HashSet::new();
        let mut result = Vec::new();
        for attr in &self.0 {
            if let Logic::Switch { on, cases } = &attr.logic {
                if on.starts_with("_root.") && seen.insert(on.clone()) {
                    let path_without_root = &on["_root.".len()..];
                    let param_name =
                        format!("root_{}", path_without_root.replace('.', "_"));
                    let param_ident = Ident::new(&param_name, Span::call_site());
                    let param_ty = discriminant_type_from_cases(cases);
                    let accessor: TokenStream = path_without_root
                        .parse()
                        .expect("kaitai_source: invalid _root ref path");
                    result.push(RootParam {
                        path: on.clone(),
                        param_ident,
                        param_ty,
                        accessor,
                    });
                }
            }
        }
        result
    }

    /// Generates variable-assignment statements for the normal `new()` body.
    ///
    /// * Inserts `buf.align_to_byte(&mut _bits_left)` whenever the sequence
    ///   transitions from a bit-field run back to byte-level reads.
    /// * Substitutes `TypeName::new_with_root(buf, …)` for any `UserDefined`
    ///   type that appears in `root_dep_map`.
    pub fn variable_assignments(
        &self,
        endianness: Endianness,
        bit_endianness: Endianness,
        root_dep_map: &HashMap<String, Vec<RootParam>>,
    ) -> Vec<TokenStream> {
        let empty_rewrite = HashMap::new();
        let mut result = Vec::new();
        let mut in_bit_run = false;

        for attr in &self.0 {
            let is_bit = attr.is_bit_field();
            if in_bit_run && !is_bit {
                result.push(quote! { buf.align_to_byte(&mut _bits_left) });
                in_bit_run = false;
            }
            if is_bit {
                in_bit_run = true;
            }
            result.push(attr.variable_assignment(
                endianness,
                bit_endianness,
                root_dep_map,
                &empty_rewrite,
            ));
        }
        result
    }

    /// Generates variable-assignment statements for a `new_with_root()` body,
    /// rewriting `_root.X.Y` switch-on expressions to the corresponding
    /// parameter identifier.
    pub fn variable_assignments_with_root_rewrite(
        &self,
        endianness: Endianness,
        bit_endianness: Endianness,
        root_rewrite: &HashMap<String, Ident>,
    ) -> Vec<TokenStream> {
        let empty_root_dep: HashMap<String, Vec<RootParam>> = HashMap::new();
        let mut result = Vec::new();
        let mut in_bit_run = false;

        for attr in &self.0 {
            let is_bit = attr.is_bit_field();
            if in_bit_run && !is_bit {
                result.push(quote! { buf.align_to_byte(&mut _bits_left) });
                in_bit_run = false;
            }
            if is_bit {
                in_bit_run = true;
            }
            result.push(attr.variable_assignment(
                endianness,
                bit_endianness,
                &empty_root_dep,
                root_rewrite,
            ));
        }
        result
    }

    pub fn field_assignments(&self) -> impl Iterator<Item = &Ident> {
        self.0.iter().filter(|a| a.is_stored()).map(|a| &a.id)
    }
}

#[derive(Clone, Debug)]
pub struct Attribute {
    pub id: Ident,
    doc: Doc,
    repeat: Option<Repeat>,
    logic: Logic,
}

impl Attribute {
    fn is_stored(&self) -> bool {
        match &self.logic {
            Logic::FixedContents(_) => false,
            Logic::Type(_) => true,
            Logic::Switch { .. } => true,
            Logic::Size(_) => true,
            Logic::Process(_) => todo!(),
        }
    }

    /// Returns `true` if this attribute reads a bit-width field (`b1`–`b64`).
    pub fn is_bit_field(&self) -> bool {
        matches!(
            &self.logic,
            Logic::Type(Type::BuiltIn {
                ty: BuiltInType::Bits(_),
                ..
            })
        )
    }

    pub fn field_definition(&self) -> TokenStream {
        let mut ty = match &self.logic {
            Logic::FixedContents(_) => return TokenStream::new(),
            Logic::Type(ty) => ty.ty(),
            Logic::Switch { cases, .. } => unify_switch_cases(cases).to_token_stream(),
            Logic::Size(_) => quote! { ::std::vec::Vec<u8> },
            Logic::Process(_) => todo!(),
        };
        if self.repeat.is_some() {
            ty = quote! { ::std::vec::Vec<#ty> };
        }

        let doc = &self.doc;
        let id = &self.id;
        quote! {
            #doc
            pub #id: #ty
        }
    }

    /// Generates the `let <id> = …;` statement for this attribute.
    ///
    /// `root_dep_map` maps a sub-type name to the `_root` params that must be
    /// forwarded via `TypeName::new_with_root(buf, …)`.
    ///
    /// `root_rewrite` maps a `_root.X.Y` string to the local parameter ident
    /// that should replace it in a `new_with_root` body.
    pub fn variable_assignment(
        &self,
        endianness: Endianness,
        bit_endianness: Endianness,
        root_dep_map: &HashMap<String, Vec<RootParam>>,
        root_rewrite: &HashMap<String, Ident>,
    ) -> TokenStream {
        let mut expr = match &self.logic {
            Logic::FixedContents(c) => {
                let contents = c.iter().map(|i| quote! { #i });
                return quote! { buf.ensure_fixed_contents(&[#(#contents),*])?; };
            }
            Logic::Type(ty) => ty.expr(endianness, bit_endianness, root_dep_map),
            Logic::Switch { on, cases } => {
                // If we're inside a `new_with_root` body, rewrite `_root.*` refs.
                let on_tokens: TokenStream = if let Some(rewrite_ident) = root_rewrite.get(on) {
                    rewrite_ident.to_token_stream()
                } else {
                    on.parse()
                        .expect("kaitai_source: invalid switch-on expression")
                };

                let unified = unify_switch_cases(cases);
                let all_bool = cases.iter().all(|(p, _)| matches!(p, Pattern::Bool(_)));

                let arms = cases.iter().map(|(pattern, ty)| {
                    let bt = match ty {
                        Type::BuiltIn { ty, en: None } => *ty,
                        _ => panic!(
                            "kaitai_source: switch-on codegen only supports built-in \
                             integer case types"
                        ),
                    };
                    let read = ty.expr(endianness, bit_endianness, root_dep_map);
                    let read = if all_bool || bt == unified {
                        read
                    } else {
                        let unified = unified.to_token_stream();
                        quote! { (#read as #unified) }
                    };
                    quote! { #pattern => #read }
                });

                if all_bool {
                    quote! {
                        match #on_tokens {
                            #(#arms),*
                        }
                    }
                } else {
                    quote! {
                        match #on_tokens {
                            #(#arms),*,
                            _ => return ::std::result::Result::Err(
                                ::kaitai::error::Error::NoEnumMatch
                            ),
                        }
                    }
                }
            }
            Logic::Size(size) => match size {
                Size::Fixed(count) => quote! { buf.read_bytes((#count) as usize)? },
                Size::Eos => quote! { buf.read_bytes_full()? },
            },
            Logic::Process(_) => todo!(),
        };

        if let Some(repeat) = &self.repeat {
            expr = match repeat {
                Repeat::Eos => {
                    quote! {
                        {
                            let mut result = Vec::new();
                            while !buf.is_eof()? {
                                result.push(#expr);
                            }
                            result
                        }
                    }
                }
                Repeat::Expr(_) => todo!(),
                Repeat::Until(_) => todo!(),
            }
        }

        let id = &self.id;
        quote! { let #id = #expr; }
    }
}

impl TryFrom<(Option<de::meta::MetaDoc>, de::attr::Attr)> for Attribute {
    type Error = ();

    fn try_from(
        (meta_doc, attr): (Option<de::meta::MetaDoc>, de::attr::Attr),
    ) -> Result<Self, Self::Error> {
        let id = Ident::new(&attr.id.unwrap(), Span::call_site());
        let doc = (meta_doc, attr.doc).into();
        let repeat = match attr.repeat {
            Some(repeat) => Some(match repeat {
                de::attr::Repeat::Eos => Repeat::Eos,
                de::attr::Repeat::Expr => Repeat::Expr(attr.repeat_expr.unwrap()),
                de::attr::Repeat::Until => Repeat::Until(attr.repeat_until.unwrap()),
            }),
            None => None,
        };
        let logic = {
            if let Some(contents) = attr.contents {
                Logic::FixedContents(contents)
            } else if let Some(size) = attr.size {
                Logic::Size(Size::Fixed(size))
            } else if attr.size_eos {
                Logic::Size(Size::Eos)
            } else {
                match attr.ty.unwrap() {
                    de::attr::AttrType::TypeRef(type_ref) => {
                        Logic::Type(Type::from((type_ref, attr.en)))
                    }
                    de::attr::AttrType::Switch {
                        switch_on: on,
                        cases,
                    } => {
                        let mut cases: Vec<(Pattern, Type)> = cases
                            .into_iter()
                            .map(|(k, v)| (Pattern::from(k), Type::from((v, None))))
                            .collect();
                        // `cases` is sourced from a `HashMap`, whose iteration
                        // order is nondeterministic; sort for stable codegen.
                        cases.sort_by(|a, b| a.0.sort_key().cmp(&b.0.sort_key()));
                        Logic::Switch { on, cases }
                    }
                }
            }
        };

        Ok(Self {
            id,
            doc,
            repeat,
            logic,
        })
    }
}

#[derive(Clone, Debug)]
pub enum Logic {
    FixedContents(Vec<u8>),
    Type(Type),
    Switch {
        on: String,
        cases: Vec<(Pattern, Type)>,
    },
    // TODO: if logic
    Size(Size),
    // TODO: probably don't use string
    Process(String),
}

// TODO: pad-right
// TODO: pos
// TODO: io
// TODO: value

#[derive(Clone, Debug)]
pub enum Type {
    UserDefined(Ident),
    BuiltIn { ty: BuiltInType, en: Option<Ident> },
}

impl Type {
    pub fn ty(&self) -> TokenStream {
        match self {
            Type::UserDefined(id) => id.into_token_stream(),
            Type::BuiltIn { ty, en } => {
                if let Some(enum_id) = en {
                    enum_id.into_token_stream()
                } else {
                    ty.to_token_stream()
                }
            }
        }
    }

    pub fn expr(
        &self,
        endianness: Endianness,
        bit_endianness: Endianness,
        root_dep_map: &HashMap<String, Vec<RootParam>>,
    ) -> TokenStream {
        match self {
            Type::UserDefined(id) => {
                if let Some(params) = root_dep_map.get(&id.to_string()) {
                    let accessors = params.iter().map(|p| &p.accessor);
                    quote! { #id::new_with_root(buf, #(#accessors),*)? }
                } else {
                    quote! { <#id as ::kaitai::KaitaiStruct>::new(buf)? }
                }
            }
            Type::BuiltIn {
                ty: BuiltInType::Bits(n),
                en: _,
            } => {
                let _ = bit_endianness; // currently only be is implemented
                if *n == 1 {
                    quote! { (buf.read_bits_be(#n, &mut _bits, &mut _bits_left)? != 0) }
                } else {
                    let rust_ty = BuiltInType::Bits(*n).to_token_stream();
                    quote! { (buf.read_bits_be(#n, &mut _bits, &mut _bits_left)? as #rust_ty) }
                }
            }
            Type::BuiltIn { ty, en } => {
                let read_call =
                    format!("buf.read_{}{}()?", ty.ks_type(), ty.endianness(endianness))
                        .parse()
                        .unwrap();
                if let Some(enum_ident) = en {
                    quote! { #enum_ident::n(#read_call).ok_or(::kaitai::error::Error::NoEnumMatch)? }
                } else {
                    read_call
                }
            }
        }
    }
}

// TODO: cow?
impl From<(String, Option<String>)> for Type {
    fn from((type_ref, en): (String, Option<String>)) -> Self {
        if let Ok(built_in) = BuiltInType::try_from(type_ref.as_ref()) {
            Type::BuiltIn {
                ty: built_in,
                en: en.map(|id| Ident::new(&sc_to_ucc(&id), Span::call_site())),
            }
        } else {
            Type::UserDefined(Ident::new(&sc_to_ucc(&type_ref), Span::call_site()))
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltInType {
    U8,
    U16,
    U32,
    U64,
    I8,
    I16,
    I32,
    I64,
    F32,
    F64,
    /// A bit-width field: `b1`–`b64`. Maps to `bool` for `b1`, widened
    /// unsigned integer for larger widths.
    Bits(u8),
}

impl TryFrom<&str> for BuiltInType {
    type Error = ();

    fn try_from(s: &str) -> Result<Self, ()> {
        Ok(match s {
            "u1" => BuiltInType::U8,
            "u2" => BuiltInType::U16,
            "u4" => BuiltInType::U32,
            "u8" => BuiltInType::U64,
            "s1" => BuiltInType::I8,
            "s2" => BuiltInType::I16,
            "s4" => BuiltInType::I32,
            "s8" => BuiltInType::I64,
            "f4" => BuiltInType::F32,
            "f8" => BuiltInType::F64,
            _ => {
                if let Some(n_str) = s.strip_prefix('b') {
                    if let Ok(n) = n_str.parse::<u8>() {
                        if n >= 1 {
                            return Ok(BuiltInType::Bits(n));
                        }
                    }
                }
                return Err(());
            }
        })
    }
}

impl BuiltInType {
    fn ks_type(&self) -> &'static str {
        match self {
            BuiltInType::U8 => "u1",
            BuiltInType::U16 => "u2",
            BuiltInType::U32 => "u4",
            BuiltInType::U64 => "u8",
            BuiltInType::I8 => "s1",
            BuiltInType::I16 => "s2",
            BuiltInType::I32 => "s4",
            BuiltInType::I64 => "s8",
            BuiltInType::F32 => "f4",
            BuiltInType::F64 => "f8",
            BuiltInType::Bits(_) => {
                unreachable!("ks_type not applicable to bit fields; handled in Type::expr")
            }
        }
    }

    fn endianness(&self, endianness: Endianness) -> &'static str {
        match &self {
            BuiltInType::U8 | BuiltInType::I8 => "",
            BuiltInType::Bits(_) => "",
            _ => endianness.into(),
        }
    }

    fn byte_width(self) -> u8 {
        match self {
            BuiltInType::U8 | BuiltInType::I8 => 1,
            BuiltInType::U16 | BuiltInType::I16 => 2,
            BuiltInType::U32 | BuiltInType::I32 | BuiltInType::F32 => 4,
            BuiltInType::U64 | BuiltInType::I64 | BuiltInType::F64 => 8,
            BuiltInType::Bits(n) => (n + 7) / 8,
        }
    }

    fn is_signed(self) -> bool {
        matches!(
            self,
            BuiltInType::I8
                | BuiltInType::I16
                | BuiltInType::I32
                | BuiltInType::I64
                | BuiltInType::F32
                | BuiltInType::F64
        )
    }

    fn is_float(self) -> bool {
        matches!(self, BuiltInType::F32 | BuiltInType::F64)
    }

    fn from_width_signed(width: u8, signed: bool) -> BuiltInType {
        match (width, signed) {
            (1, false) => BuiltInType::U8,
            (2, false) => BuiltInType::U16,
            (4, false) => BuiltInType::U32,
            (8, false) => BuiltInType::U64,
            (1, true) => BuiltInType::I8,
            (2, true) => BuiltInType::I16,
            (4, true) => BuiltInType::I32,
            (8, true) => BuiltInType::I64,
            _ => unreachable!("invalid integer width {width}"),
        }
    }
}

impl ToTokens for BuiltInType {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        tokens.extend(match self {
            BuiltInType::U8 => quote! { u8 },
            BuiltInType::U16 => quote! { u16 },
            BuiltInType::U32 => quote! { u32 },
            BuiltInType::U64 => quote! { u64 },
            BuiltInType::I8 => quote! { i8 },
            BuiltInType::I16 => quote! { i16 },
            BuiltInType::I32 => quote! { i32 },
            BuiltInType::I64 => quote! { i64 },
            BuiltInType::F32 => quote! { f32 },
            BuiltInType::F64 => quote! { f64 },
            BuiltInType::Bits(1) => quote! { bool },
            BuiltInType::Bits(n) if *n <= 8 => quote! { u8 },
            BuiltInType::Bits(n) if *n <= 16 => quote! { u16 },
            BuiltInType::Bits(n) if *n <= 32 => quote! { u32 },
            BuiltInType::Bits(_) => quote! { u64 },
        })
    }
}

// TODO: Encoding field on String type
// TODO: terminator for String or Byte array

#[derive(Clone, Debug)]
pub enum Pattern {
    Enum(String),
    Int(u64),
    Bool(bool),
}

impl From<String> for Pattern {
    fn from(s: String) -> Self {
        if s == "true" {
            return Pattern::Bool(true);
        }
        if s == "false" {
            return Pattern::Bool(false);
        }
        match s.parse::<u64>() {
            Ok(n) => Pattern::Int(n),
            Err(_) => Pattern::Enum(s),
        }
    }
}

impl Pattern {
    fn sort_key(&self) -> (u8, u64, &str) {
        match self {
            Pattern::Int(n) => (0, *n, ""),
            Pattern::Bool(b) => (1, if *b { 1 } else { 0 }, ""),
            Pattern::Enum(s) => (2, 0, s.as_str()),
        }
    }
}

impl ToTokens for Pattern {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            Pattern::Int(n) => proc_macro2::Literal::u64_unsuffixed(*n).to_tokens(tokens),
            Pattern::Bool(b) => {
                let t: TokenStream = if *b { quote! { true } } else { quote! { false } };
                tokens.extend(t);
            }
            Pattern::Enum(s) => {
                // `enum_name::value` -> `EnumName::Value`
                let path = s.split("::").map(sc_to_ucc).collect::<Vec<_>>().join("::");
                let path: TokenStream = path
                    .parse()
                    .expect("kaitai_source: invalid enum pattern in switch case");
                tokens.extend(path);
            }
        }
    }
}

/// Derives the Rust discriminant type required by a set of switch cases.
/// Bool-pattern cases → `bool`; integer-pattern cases → widened integer type.
fn discriminant_type_from_cases(cases: &[(Pattern, Type)]) -> TokenStream {
    if cases.iter().all(|(p, _)| matches!(p, Pattern::Bool(_))) {
        quote! { bool }
    } else {
        unify_switch_cases(cases).to_token_stream()
    }
}

/// Computes the unified Rust type for a set of switch cases. Only built-in
/// integer case types are supported; they are widened to the smallest type
/// that fits every case (e.g. `u1` + `u2` -> `u16`).
fn unify_switch_cases(cases: &[(Pattern, Type)]) -> BuiltInType {
    let mut types = cases.iter().map(|(_, ty)| match ty {
        Type::BuiltIn { ty, en: None } => *ty,
        _ => panic!(
            "kaitai_source: switch-on codegen only supports built-in integer case \
             types (no user-defined types or enum-typed cases)"
        ),
    });
    let mut unified = types
        .next()
        .expect("kaitai_source: switch-on must have at least one case");
    for ty in types {
        unified = widen(unified, ty);
    }
    unified
}

fn widen(a: BuiltInType, b: BuiltInType) -> BuiltInType {
    if a == b {
        return a;
    }
    if matches!(a, BuiltInType::Bits(_)) || matches!(b, BuiltInType::Bits(_)) {
        panic!("kaitai_source: bit types cannot be used as switch-on case types");
    }
    if a.is_float() || b.is_float() {
        panic!("kaitai_source: switch-on cannot unify differing float and integer case types");
    }
    if a.is_signed() != b.is_signed() {
        panic!(
            "kaitai_source: switch-on cannot unify signed and unsigned case types; \
             make all cases the same signedness"
        );
    }
    BuiltInType::from_width_signed(a.byte_width().max(b.byte_width()), a.is_signed())
}

#[derive(Clone, Debug)]
pub enum Size {
    Fixed(IntegerValue),
    Eos,
}

#[derive(Clone, Debug)]
pub enum Repeat {
    Eos,
    Expr(IntegerValue),
    Until(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn attribute_field_definitions() {
        let docs = (0..5).map(|_| Doc::new());
        let repeats = vec![
            Some(Repeat::Eos),
            None,
            None,
            Some(Repeat::Eos),
            Some(Repeat::Eos),
        ];
        let logics = vec![
            Logic::FixedContents(vec![0, 1]),
            Logic::Type(Type::UserDefined(Ident::new("MyType", Span::call_site()))),
            Logic::Type(Type::BuiltIn {
                ty: BuiltInType::U16,
                en: None,
            }),
            Logic::Type(Type::BuiltIn {
                ty: BuiltInType::U16,
                en: Some(Ident::new("MyEnum", Span::call_site())),
            }),
            Logic::Size(Size::Eos),
        ];

        let expected = vec![
            quote! {},
            quote! {
                #[doc = ""]
                pub dont: MyType
            },
            quote! {
                #[doc = ""]
                pub kill: u16
            },
            quote! {
                #[doc = ""]
                pub my: ::std::vec::Vec<MyEnum>
            },
            quote! {
                #[doc = ""]
                // Yes the space has to be there. No I don't know why.
                pub vibe: ::std::vec::Vec<::std::vec::Vec<u8> >
            },
        ];
        vec!["bitch", "dont", "kill", "my", "vibe"]
            .iter()
            .map(|id| Ident::new(id, Span::call_site()))
            .zip(docs)
            .zip(repeats)
            .zip(logics)
            .map(|(((id, doc), repeat), logic)| {
                Attribute {
                    id,
                    doc,
                    repeat,
                    logic,
                }
                .field_definition()
            })
            .zip(expected)
            .for_each(|(def, expected)| assert_eq!(def.to_string(), expected.to_string()));
    }
}
