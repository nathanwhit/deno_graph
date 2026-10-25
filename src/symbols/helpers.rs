// Copyright 2018-2024 the Deno authors. MIT license.

use deno_ast::oxc::ast::ast::BindingIdentifier;
use deno_ast::oxc::ast::ast::ExportAllDeclaration;
use deno_ast::oxc::ast::ast::IdentifierName;
use deno_ast::oxc::ast::ast::IdentifierReference;
use deno_ast::oxc::ast::ast::TSQualifiedName;
use deno_ast::oxc::ast::ast::TSTypeName;
use deno_ast::oxc::semantic::Scoping;
use deno_ast::oxc::span::GetSpan;
use deno_ast::oxc::span::Span;

/// In OXC, the equivalent of SWC's `Id` is `(String, usize)`. The second
/// component is a scope discriminator: SWC uses a `SyntaxContext`, and the
/// OXC equivalent is the resolved symbol id from semantic analysis. `0` means
/// "unresolved" (a global, or a context-free property/member name) and never
/// collides with a real symbol because real symbols are stored as
/// `symbol_id + 1`.
pub type Id = (String, usize);

/// Discriminator value used when an identifier has no resolved symbol.
const UNRESOLVED_CTXT: usize = 0;

/// Whether the id refers to an unresolved binding (a global or an identifier
/// that was created after semantic analysis).
pub fn is_unresolved_id(id: &Id) -> bool {
  id.1 == UNRESOLVED_CTXT
}

fn symbol_ctxt(symbol_id: deno_ast::oxc::semantic::SymbolId) -> usize {
  symbol_id.index() + 1
}

/// Trait to convert various identifier types to an `Id`. `scoping` is the
/// semantic analysis result; when present it disambiguates same-named symbols
/// across scopes (the SWC `SyntaxContext` equivalent).
pub trait ToId {
  fn to_id(&self, scoping: Option<&Scoping>) -> Id;
}

impl ToId for BindingIdentifier<'_> {
  fn to_id(&self, _scoping: Option<&Scoping>) -> Id {
    // A binding's resolved symbol id is stored directly on the node by
    // semantic analysis.
    let ctxt = self
      .symbol_id
      .get()
      .map(symbol_ctxt)
      .unwrap_or(UNRESOLVED_CTXT);
    (self.name.to_string(), ctxt)
  }
}

impl ToId for IdentifierReference<'_> {
  fn to_id(&self, scoping: Option<&Scoping>) -> Id {
    // A reference resolves to a symbol via the scoping's reference table.
    let ctxt = self
      .reference_id
      .get()
      .zip(scoping)
      .and_then(|(reference_id, scoping)| {
        scoping.get_reference(reference_id).symbol_id()
      })
      .map(symbol_ctxt)
      .unwrap_or(UNRESOLVED_CTXT);
    (self.name.to_string(), ctxt)
  }
}

impl ToId for IdentifierName<'_> {
  fn to_id(&self, _scoping: Option<&Scoping>) -> Id {
    // A property/member name is resolved structurally, not by scope.
    (self.name.to_string(), UNRESOLVED_CTXT)
  }
}

pub fn ts_entity_name_to_parts(
  entity_name: &TSTypeName,
  scoping: Option<&Scoping>,
) -> (Id, Vec<String>) {
  match entity_name {
    TSTypeName::QualifiedName(qualified_name) => {
      ts_qualified_name_parts(qualified_name, scoping)
    }
    TSTypeName::IdentifierReference(ident) => {
      (ident.to_id(scoping), Vec::new())
    }
    TSTypeName::ThisExpression(_) => {
      (("this".to_string(), UNRESOLVED_CTXT), Vec::new())
    }
  }
}

pub fn ts_qualified_name_parts(
  mut qualified_name: &TSQualifiedName,
  scoping: Option<&Scoping>,
) -> (Id, Vec<String>) {
  let mut parts = Vec::new();
  loop {
    parts.push(qualified_name.right.name.to_string());
    match &qualified_name.left {
      TSTypeName::QualifiedName(n) => {
        qualified_name = n;
      }
      TSTypeName::IdentifierReference(n) => {
        parts.reverse();
        return (n.to_id(scoping), parts);
      }
      TSTypeName::ThisExpression(_) => {
        parts.reverse();
        return (("this".to_string(), UNRESOLVED_CTXT), parts);
      }
    }
  }
}

/// The span of the `* as name` part of `export * as name from "..."` (the
/// specifier span swc reported for it), or the whole declaration for a bare
/// `export * from "..."`.
pub fn export_all_specifier_span(
  n: &ExportAllDeclaration,
  source_text: &str,
) -> Span {
  let Some(exported) = &n.exported else {
    return n.span;
  };
  let exported_span = exported.span();
  let start = source_text
    .get(n.span.start as usize..exported_span.start as usize)
    .and_then(|text| text.find('*'))
    .map(|index| n.span.start + index as u32)
    .unwrap_or(n.span.start);
  Span::new(start, exported_span.end)
}
