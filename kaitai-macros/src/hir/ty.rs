use crate::{
    de,
    hir::{
        attr::{Attribute, Attributes, RootParam},
        doc::Doc,
        en::Enumeration,
        meta::Endianness,
        param::Parameter,
    },
    util::sc_to_ucc,
};

use std::collections::HashMap;

use proc_macro2::{Ident, Span};
use quote::ToTokens;

#[derive(Debug)]
pub struct Type {
    id: Ident,
    endianness: Endianness,
    bit_endianness: Endianness,
    doc: Doc,
    params: Vec<Parameter>,
    seq: Attributes,
    types: Vec<Type>,
    instances: HashMap<String, Attribute>,
    enums: Vec<Enumeration>,
}

pub struct InheritedMeta {
    pub id: Option<(Ident, bool)>,
    pub endianness: Option<Endianness>,
    pub bit_endianness: Option<Endianness>,
}

impl Type {
    /// Returns the list of `_root.X.Y` switch-on dependencies in this type's
    /// own seq — used by the parent to build a `root_dep_map` for call-site
    /// substitution.
    pub fn root_refs(&self) -> Vec<RootParam> {
        self.seq.root_refs()
    }

    pub fn type_ident(&self) -> &Ident {
        &self.id
    }
}

impl TryFrom<(InheritedMeta, de::ty::Type)> for Type {
    type Error = ();

    fn try_from((inherited_meta, ty): (InheritedMeta, de::ty::Type)) -> Result<Self, Self::Error> {
        let meta_id = ty.meta.as_ref().and_then(|m| {
            m.id.as_ref()
                .map(|id| Ident::new(&sc_to_ucc(id), Span::call_site()))
        });
        let id = match inherited_meta.id {
            Some((id, overwrite)) => {
                if overwrite {
                    id
                } else if let Some(id) = meta_id {
                    id
                } else {
                    id
                }
            }
            None => meta_id.unwrap(),
        };

        let endianness = ty
            .meta
            .as_ref()
            .and_then(|m| m.endianness)
            .or(inherited_meta.endianness)
            .expect("no endianness inherited");

        let bit_endianness = ty
            .meta
            .as_ref()
            .and_then(|m| m.bit_endian)
            .or(inherited_meta.bit_endianness)
            .unwrap_or(Endianness::Be);

        // TODO: All the meta doc clones.
        let doc = (ty.meta.as_ref().map(|meta| meta.doc.clone()), ty.doc).into();
        let seq = (ty.meta.as_ref().map(|m| m.doc.clone()), ty.seq)
            .try_into()
            .expect("seq validation failed");
        let types = ty
            .types
            .into_iter()
            .map(|(id, ty)| {
                let inherited_meta = InheritedMeta {
                    id: Some((Ident::new(&sc_to_ucc(&id), Span::call_site()), false)),
                    endianness: Some(endianness),
                    bit_endianness: Some(bit_endianness),
                };
                Type::try_from((inherited_meta, ty)).expect("type validation failed")
            })
            .collect();
        let enums = ty
            .enums
            .into_iter()
            .map(|(id, en)| (id.as_ref(), en).into())
            .collect();

        Ok(Self {
            id,
            endianness,
            bit_endianness,
            doc,
            // TODO
            params: Default::default(),
            seq,
            types,
            // TODO
            instances: Default::default(),
            enums,
        })
    }
}

impl ToTokens for Type {
    fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
        // Build the root-dependency map: sub-types that reference `_root.*` in
        // their switch-on expressions need to be called via `new_with_root`
        // rather than the standard `KaitaiStruct::new`.
        let mut root_dep_map: HashMap<String, Vec<RootParam>> = HashMap::new();
        for sub_ty in &self.types {
            let refs = sub_ty.root_refs();
            if !refs.is_empty() {
                root_dep_map.insert(sub_ty.id.to_string(), refs);
            }
        }

        let type_defs = self.types.iter().map(|ty| ty.into_token_stream());
        let enum_defs = self.enums.iter().map(|en| en.into_token_stream());
        let doc = &self.doc;
        let id = &self.id;
        let field_defs = self.seq.field_definitions();

        let var_assignments =
            self.seq
                .variable_assignments(self.endianness, self.bit_endianness, &root_dep_map);
        let field_assignments: Vec<&Ident> = self.seq.field_assignments().collect();

        let has_bits = self.seq.has_bit_fields();
        let bits_init = if has_bits {
            quote::quote! {
                let mut _bits: u64 = 0u64;
                let mut _bits_left: u8 = 0u8;
            }
        } else {
            proc_macro2::TokenStream::new()
        };

        // If this type's own seq references `_root.*`, its `KaitaiStruct::new`
        // cannot be used standalone; generate a stub and a `new_with_root`
        // associated function instead.
        let own_root_refs = self.seq.root_refs();
        let has_root_deps = !own_root_refs.is_empty();

        let new_impl = if has_root_deps {
            quote::quote! {
                fn new<S: ::kaitai::__private::KaitaiStream>(_buf: &mut S) -> ::kaitai::error::Result<Self> {
                    unimplemented!("this type requires _root context; call new_with_root instead")
                }
            }
        } else {
            quote::quote! {
                fn new<S: ::kaitai::__private::KaitaiStream>(buf: &mut S) -> ::kaitai::error::Result<Self> {
                    #bits_init
                    #(#var_assignments);*;
                    Ok(Self {
                        #(#field_assignments),*
                    })
                }
            }
        };

        tokens.extend(quote::quote! {
            #(#type_defs)*
            #(#enum_defs)*

            #doc
            // TODO: Pass down attributes from struct
            #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
            pub struct #id {
                #(#field_defs),*
            }

            #[automatically_derived]
            impl ::kaitai::KaitaiStruct for #id {
                #new_impl
                fn read<S: ::kaitai::__private::KaitaiStream>(&mut self, _: &mut S) -> ::kaitai::error::Result<()> {
                    todo!();
                }
            }
        });

        // Generate the `new_with_root` associated function for types that have
        // `_root.*` dependencies.
        if has_root_deps {
            let root_rewrite: HashMap<String, Ident> = own_root_refs
                .iter()
                .map(|rp| (rp.path.clone(), rp.param_ident.clone()))
                .collect();

            let new_with_root_var_assignments = self.seq.variable_assignments_with_root_rewrite(
                self.endianness,
                self.bit_endianness,
                &root_rewrite,
            );

            let root_bits_init = if has_bits {
                quote::quote! {
                    let mut _bits: u64 = 0u64;
                    let mut _bits_left: u8 = 0u8;
                }
            } else {
                proc_macro2::TokenStream::new()
            };

            let params = own_root_refs.iter().map(|rp| {
                let name = &rp.param_ident;
                let ty = &rp.param_ty;
                quote::quote! { #name: #ty }
            });

            let field_assignments_root: Vec<&Ident> = self.seq.field_assignments().collect();

            tokens.extend(quote::quote! {
                impl #id {
                    pub fn new_with_root<S: ::kaitai::__private::KaitaiStream>(
                        buf: &mut S,
                        #(#params),*
                    ) -> ::kaitai::error::Result<Self> {
                        #root_bits_init
                        #(#new_with_root_var_assignments);*;
                        Ok(Self {
                            #(#field_assignments_root),*
                        })
                    }
                }
            });
        }
    }
}
