use deno_ast::ModuleSpecifier;
use deno_ast::SourceTextInfo;
use deno_ast::oxc::allocator::Allocator;
use deno_ast::oxc::allocator::Box;
use deno_ast::oxc::allocator::CloneIn;
use deno_ast::oxc::allocator::Vec;
use deno_ast::oxc::ast::ast::*;
use deno_ast::oxc::ast::builder::AstBuilder;
use deno_ast::oxc::semantic::Scoping;
use deno_ast::oxc::span::GetSpan;
use deno_ast::oxc::span::Ident;
use deno_ast::oxc::span::SPAN;
use deno_ast::oxc::span::Span;
use deno_ast::oxc::syntax::operator::UnaryOperator;
use std::collections::HashSet;

use super::FastCheckDiagnosticRange;
use super::helpers::DeclMutabilityKind;
use super::helpers::TSKeywordKind;
use super::helpers::any_type_ann;
use super::helpers::is_global_ident;
use super::helpers::maybe_lit_to_ts_type;
use super::helpers::new_ident;
use super::helpers::object_freeze_call_arg;
use super::helpers::tpl_to_ts_type;
use super::helpers::ts_keyword_type;
use super::helpers::ts_readonly;
use super::helpers::ts_tuple_element;
use super::helpers::type_ann;
use super::range_finder::ModulePublicRanges;
use crate::symbols::helpers::Id;
use crate::symbols::helpers::ToId;

#[derive(Debug, Clone, thiserror::Error)]
pub enum FastCheckDtsDiagnostic {
  #[error("unable to infer type from expression or declaration")]
  UnableToInferType { range: FastCheckDiagnosticRange },
  #[error("unable to infer type, falling back to any type")]
  UnableToInferTypeFallbackAny { range: FastCheckDiagnosticRange },
  #[error("unable to infer type from object property, skipping")]
  UnableToInferTypeFromProp { range: FastCheckDiagnosticRange },
  #[error("unable to infer type from spread, skipping")]
  UnableToInferTypeFromSpread { range: FastCheckDiagnosticRange },
  #[error("cannot infer type from using, skipping")]
  UnsupportedUsing { range: FastCheckDiagnosticRange },
}

impl FastCheckDtsDiagnostic {
  pub fn specifier(&self) -> &ModuleSpecifier {
    match self {
      FastCheckDtsDiagnostic::UnableToInferType { range } => &range.specifier,
      FastCheckDtsDiagnostic::UnableToInferTypeFallbackAny { range } => {
        &range.specifier
      }
      FastCheckDtsDiagnostic::UnableToInferTypeFromProp { range } => {
        &range.specifier
      }
      FastCheckDtsDiagnostic::UnableToInferTypeFromSpread { range } => {
        &range.specifier
      }
      FastCheckDtsDiagnostic::UnsupportedUsing { range } => &range.specifier,
    }
  }

  pub fn range(&self) -> &FastCheckDiagnosticRange {
    match self {
      FastCheckDtsDiagnostic::UnableToInferType { range } => range,
      FastCheckDtsDiagnostic::UnableToInferTypeFallbackAny { range } => range,
      FastCheckDtsDiagnostic::UnableToInferTypeFromProp { range } => range,
      FastCheckDtsDiagnostic::UnableToInferTypeFromSpread { range } => range,
      FastCheckDtsDiagnostic::UnsupportedUsing { range } => range,
    }
  }
}

pub struct FastCheckDtsTransformer<'a, 'b> {
  allocator: &'a Allocator,
  id_counter: usize,
  text_info: &'b SourceTextInfo,
  public_ranges: &'b ModulePublicRanges,
  pub diagnostics: std::vec::Vec<FastCheckDtsDiagnostic>,
  specifier: &'b ModuleSpecifier,
  scoping: Option<&'b Scoping>,
  /// Bindings that are known to have a non-widening inferable type, so
  /// referencing them via `typeof` in the emitted declaration is sound
  /// (function and class declarations, and consts that are explicitly
  /// typed or initialized with a function).
  typeof_safe_ids: HashSet<Id>,
  /// Module level class declarations without type parameters, whose `new`
  /// expressions have the class instance type.
  non_generic_class_ids: HashSet<Id>,
  /// Module level bindings known to have an array or tuple type, which is
  /// required for a `...typeof ident` tuple rest element to be valid.
  array_typed_ids: HashSet<Id>,
  is_top_level: bool,
}

impl<'a, 'b> FastCheckDtsTransformer<'a, 'b> {
  pub fn new(
    allocator: &'a Allocator,
    text_info: &'b SourceTextInfo,
    public_ranges: &'b ModulePublicRanges,
    specifier: &'b ModuleSpecifier,
    scoping: Option<&'b Scoping>,
  ) -> Self {
    Self {
      allocator,
      id_counter: 0,
      text_info,
      specifier,
      public_ranges,
      diagnostics: vec![],
      scoping,
      typeof_safe_ids: HashSet::new(),
      non_generic_class_ids: HashSet::new(),
      array_typed_ids: HashSet::new(),
      is_top_level: true,
    }
  }

  fn builder(&self) -> AstBuilder<'a> {
    AstBuilder::new(self.allocator)
  }

  fn gen_unique_name(&mut self) -> String {
    self.id_counter += 1;
    format!("_dts_{}", self.id_counter)
  }

  fn mark_diagnostic(&mut self, diagnostic: FastCheckDtsDiagnostic) {
    self.diagnostics.push(diagnostic)
  }

  fn source_range_to_range(&self, range: Span) -> FastCheckDiagnosticRange {
    FastCheckDiagnosticRange {
      specifier: self.specifier.clone(),
      text_info: self.text_info.clone(),
      range,
    }
  }

  fn mark_diagnostic_unable_to_infer(&mut self, range: Span) {
    self.mark_diagnostic(FastCheckDtsDiagnostic::UnableToInferType {
      range: self.source_range_to_range(range),
    })
  }

  fn mark_diagnostic_any_fallback(&mut self, range: Span) {
    self.mark_diagnostic(FastCheckDtsDiagnostic::UnableToInferTypeFallbackAny {
      range: self.source_range_to_range(range),
    })
  }

  fn mark_diagnostic_unsupported_prop(&mut self, range: Span) {
    self.mark_diagnostic(FastCheckDtsDiagnostic::UnableToInferTypeFromProp {
      range: self.source_range_to_range(range),
    })
  }

  pub fn transform(&mut self, mut program: Program<'a>) -> Program<'a> {
    self.is_top_level = true;
    let prescanned_ids = prescan_module_ids(&program, self.scoping);
    self.typeof_safe_ids = prescanned_ids.typeof_safe;
    self.non_generic_class_ids = prescanned_ids.non_generic_classes;
    self.array_typed_ids = prescanned_ids.array_typed;
    let body =
      std::mem::replace(&mut program.body, Vec::new_in(&self.allocator));
    program.body = self.transform_stmts(body);
    program
  }

  fn transform_stmts(
    &mut self,
    body: Vec<'a, Statement<'a>>,
  ) -> Vec<'a, Statement<'a>> {
    let mut new_items: Vec<'a, Statement<'a>> = Vec::new_in(&self.allocator);

    for item in body {
      match item {
        Statement::ImportDeclaration(_) => {
          new_items.push(item);
        }
        Statement::ExportDeclaration(export_decl) => {
          if let Declaration::FunctionDeclaration(_) = &export_decl.declaration
            && self.public_ranges.is_impl_with_overloads(&export_decl.span)
          {
            continue; // skip implementation signature
          }

          match self.decl_to_type_decl(
            export_decl
              .declaration
              .clone_in_with_semantic_ids(self.allocator),
          ) {
            Some(new_decl) => {
              new_items.push(Statement::new_export_declaration(
                export_decl.span,
                new_decl,
                &AstBuilder::new(self.allocator),
              ));
            }
            _ => {
              self.mark_diagnostic(FastCheckDtsDiagnostic::UnableToInferType {
                range: self.source_range_to_range(export_decl.span),
              })
            }
          }
        }
        // `export { foo }` and `export { foo } from "bar"` - keep as is
        Statement::ExportNamedDeclaration(_)
        | Statement::ExportFromDeclaration(_) => {
          new_items.push(item);
        }
        Statement::ExportDefaultDeclaration(export_decl) => {
          match &export_decl.declaration {
            ExportDefaultDeclarationKind::ClassDeclaration(_) => {
              let mut cloned =
                export_decl.clone_in_with_semantic_ids(self.allocator);
              if let ExportDefaultDeclarationKind::ClassDeclaration(
                ref mut class_expr,
              ) = cloned.declaration
              {
                class_expr.body = self.class_body_to_type(&class_expr.body);
              }
              new_items.push(Statement::ExportDefaultDeclaration(cloned));
            }
            ExportDefaultDeclarationKind::FunctionDeclaration(_) => {
              if self.public_ranges.is_impl_with_overloads(&export_decl.span) {
                continue; // skip implementation signature
              }

              let mut cloned =
                export_decl.clone_in_with_semantic_ids(self.allocator);
              if let ExportDefaultDeclarationKind::FunctionDeclaration(
                ref mut fn_expr,
              ) = cloned.declaration
              {
                fn_expr.body = None;
              }
              new_items.push(Statement::ExportDefaultDeclaration(cloned));
            }
            ExportDefaultDeclarationKind::TSInterfaceDeclaration(_) => {
              new_items.push(Statement::ExportDefaultDeclaration(export_decl));
            }
            _ => {
              // Expression variant - handle like ExportDefaultExpr.
              // A default export of an identifier can reference the
              // declaration directly without an intermediate variable.
              if let ExportDefaultDeclarationKind::Identifier(_) =
                &export_decl.declaration
              {
                new_items
                  .push(Statement::ExportDefaultDeclaration(export_decl));
                continue;
              }
              let expr = Some(
                export_decl
                  .declaration
                  .clone_in_with_semantic_ids(self.allocator)
                  .into_expression(),
              );

              if let Some(expr) = expr {
                let name = self.gen_unique_name();
                let name_ident = new_ident(self.allocator, &name);
                let type_ann_opt = self
                  .expr_to_ts_type(&expr, false, true)
                  .map(|t| type_ann(self.allocator, t));

                if let Some(ta) = type_ann_opt {
                  // Create: declare const _dts_N: Type;
                  let mut declarations = Vec::new_in(&self.allocator);
                  declarations.push(VariableDeclarator::new(
                    SPAN,
                    BindingPattern::BindingIdentifier(Box::new_in(
                      name_ident.clone_in_with_semantic_ids(self.allocator),
                      &self.allocator,
                    )),
                    Some(ta),
                    None,
                    false,
                    &AstBuilder::new(self.allocator),
                  ));
                  new_items.push(Statement::VariableDeclaration(Box::new_in(
                    VariableDeclaration::new(
                      SPAN,
                      VariableDeclarationKind::Const,
                      declarations,
                      true,
                      &AstBuilder::new(self.allocator),
                    ),
                    &self.allocator,
                  )));

                  // Create: export default _dts_N;
                  new_items.push(Statement::ExportDefaultDeclaration(
                    Box::new_in(
                      ExportDefaultDeclaration::new(
                        export_decl.span,
                        ExportDefaultDeclarationKind::Identifier(Box::new_in(
                          IdentifierReference::new(
                            SPAN,
                            Ident::from(self.allocator.alloc_str(&name)),
                            &AstBuilder::new(self.allocator),
                          ),
                          &self.allocator,
                        )),
                        &AstBuilder::new(self.allocator),
                      ),
                      &self.allocator,
                    ),
                  ));
                } else {
                  // Re-emit with original expression
                  let kind = ExportDefaultDeclarationKind::from(expr);
                  new_items.push(Statement::ExportDefaultDeclaration(
                    Box::new_in(
                      ExportDefaultDeclaration::new(
                        export_decl.span,
                        kind,
                        &AstBuilder::new(self.allocator),
                      ),
                      &self.allocator,
                    ),
                  ));
                }
              }
            }
          }
        }
        // Keep all these
        Statement::TSImportEqualsDeclaration(_)
        | Statement::TSNamespaceExportDeclaration(_)
        | Statement::TSExportAssignment(_)
        | Statement::ExportAllDeclaration(_) => {
          new_items.push(item);
        }
        _ => {
          // Regular statements and declarations
          if let Some(new_stmt) = self.transform_module_stmt(item) {
            new_items.push(new_stmt);
          }
        }
      }
    }

    new_items
  }

  fn transform_module_stmt(
    &mut self,
    stmt: Statement<'a>,
  ) -> Option<Statement<'a>> {
    // Extract the declaration from a statement
    if !stmt.is_declaration() {
      return None;
    }
    let decl = stmt.into_declaration();

    if let Declaration::FunctionDeclaration(_) = &decl
      && self.public_ranges.is_impl_with_overloads(&decl.span())
    {
      return None; // skip implementation signature
    }

    match &decl {
      Declaration::VariableDeclaration(var_decl)
        if matches!(
          var_decl.kind,
          VariableDeclarationKind::Using | VariableDeclarationKind::AwaitUsing
        ) =>
      {
        Some(Statement::from(decl))
      }
      Declaration::TSEnumDeclaration(_)
      | Declaration::ClassDeclaration(_)
      | Declaration::FunctionDeclaration(_)
      | Declaration::VariableDeclaration(_)
      | Declaration::TSNamespaceDeclaration(_) => {
        match self
          .decl_to_type_decl(decl.clone_in_with_semantic_ids(self.allocator))
        {
          Some(new_decl) => Some(Statement::from(new_decl)),
          _ => {
            self.mark_diagnostic_unable_to_infer(decl.span());
            None
          }
        }
      }
      Declaration::TSInterfaceDeclaration(_)
      | Declaration::TSTypeAliasDeclaration(_)
      | Declaration::TSGlobalDeclaration(_)
      | Declaration::TSExternalModuleDeclaration(_)
      | Declaration::TSImportEqualsDeclaration(_) => {
        Some(Statement::from(decl))
      }
    }
  }

  fn expr_to_ts_type(
    &mut self,
    expr: &Expression<'a>,
    as_const: bool,
    as_readonly: bool,
  ) -> Option<TSType<'a>> {
    match expr {
      Expression::ArrayExpression(arr) => {
        let mut elem_types: std::vec::Vec<TSTupleElement<'a>> = vec![];

        for elem in &arr.elements {
          match elem {
            ArrayExpressionElement::Elision(_) => {
              // TypeScript converts holey arrays to any
              elem_types.push(ts_tuple_element(ts_keyword_type(
                self.allocator,
                TSKeywordKind::Any,
              )));
            }
            ArrayExpressionElement::SpreadElement(spread) => {
              // tuple types support spreading array types, so a spread of
              // an identifier known to be array-typed can be represented
              // as `...typeof ident` and a spread of an array literal as a
              // rest of its tuple type
              let rest_type = match &spread.argument {
                Expression::Identifier(ident)
                  if self
                    .array_typed_ids
                    .contains(&ident.to_id(self.scoping)) =>
                {
                  Some(TSType::new_ts_type_query(
                    SPAN,
                    TSTypeQueryExprName::new_identifier_reference(
                      SPAN,
                      ident.name,
                      &self.builder(),
                    ),
                    None,
                    &self.builder(),
                  ))
                }
                Expression::ArrayExpression(_) => {
                  self.expr_to_ts_type(&spread.argument, as_const, false)
                }
                _ => None,
              };
              match rest_type {
                Some(rest_type) => {
                  elem_types.push(TSTupleElement::new_ts_rest_type(
                    SPAN,
                    rest_type,
                    &self.builder(),
                  ));
                }
                None => {
                  // give up on the whole array rather than emitting a
                  // tuple type that is missing elements
                  self.mark_diagnostic(
                    FastCheckDtsDiagnostic::UnableToInferTypeFromSpread {
                      range: self.source_range_to_range(spread.span),
                    },
                  );
                  return None;
                }
              }
            }
            _ => {
              // Expression variants
              if let Some(e) = elem.as_expression() {
                match self.expr_to_ts_type(e, as_const, as_readonly) {
                  Some(ts_expr) => {
                    elem_types.push(ts_tuple_element(ts_expr));
                  }
                  _ => {
                    // fall back to `any` for the element so the tuple
                    // keeps the correct number of elements
                    self.mark_diagnostic_unable_to_infer(e.span());
                    elem_types.push(ts_tuple_element(ts_keyword_type(
                      self.allocator,
                      TSKeywordKind::Any,
                    )));
                  }
                }
              }
            }
          }
        }

        let mut oxc_elem_types = Vec::new_in(&self.allocator);
        for et in elem_types {
          oxc_elem_types.push(et);
        }

        let mut result = TSType::TSTupleType(Box::new_in(
          TSTupleType::new(
            arr.span,
            oxc_elem_types,
            &AstBuilder::new(self.allocator),
          ),
          &self.allocator,
        ));

        if as_readonly {
          result = ts_readonly(self.allocator, result);
        }
        Some(result)
      }
      Expression::ObjectExpression(obj) => {
        let mut members: std::vec::Vec<TSSignature<'a>> = vec![];

        for item in &obj.properties {
          match item {
            ObjectPropertyKind::ObjectProperty(prop) => {
              if prop.shorthand {
                // `{ ident }` - reference the binding's type via `typeof`
                // when that is sound
                let ts_type = match &prop.value {
                  Expression::Identifier(ident) => {
                    self.ident_to_ts_type(ident, as_const)
                  }
                  _ => None,
                };
                match ts_type {
                  Some(ts_type) => {
                    members.push(TSSignature::new_ts_property_signature(
                      SPAN,
                      false,
                      false,
                      as_readonly,
                      prop.key.clone_in_with_semantic_ids(self.allocator),
                      Some(type_ann(self.allocator, ts_type)),
                      &self.builder(),
                    ));
                  }
                  None => {
                    self.mark_diagnostic_unsupported_prop(prop.span);
                  }
                }
                continue;
              }

              if prop.method {
                // Convert method to TSMethodSignature
                if let Expression::FunctionExpression(func) = &prop.value {
                  let (key, computed) =
                    self.prop_key_to_expr_key(&prop.key, prop.computed);
                  let kind = match prop.kind {
                    PropertyKind::Get => TSMethodSignatureKind::Get,
                    PropertyKind::Set => TSMethodSignatureKind::Set,
                    _ => TSMethodSignatureKind::Method,
                  };
                  members.push(TSSignature::TSMethodSignature(Box::new_in(
                    TSMethodSignature::new(
                      SPAN,
                      key,
                      computed,
                      false,
                      kind,
                      func
                        .type_parameters
                        .clone_in_with_semantic_ids(self.allocator),
                      func
                        .this_param
                        .clone_in_with_semantic_ids(self.allocator),
                      func.params.clone_in_with_semantic_ids(self.allocator),
                      func
                        .return_type
                        .clone_in_with_semantic_ids(self.allocator),
                      &AstBuilder::new(self.allocator),
                    ),
                    &self.allocator,
                  )));
                } else {
                  self.mark_diagnostic_unsupported_prop(prop.span);
                }
                continue;
              }

              if prop.kind != PropertyKind::Init {
                // getter/setter without method flag
                self.mark_diagnostic_unsupported_prop(prop.span);
                continue;
              }

              let (key, computed) =
                self.prop_key_to_expr_key(&prop.key, prop.computed);

              let init_type = match self.expr_to_ts_type(
                &prop.value,
                as_const,
                as_readonly,
              ) {
                Some(ts_type) => type_ann(self.allocator, ts_type),
                None => {
                  self.mark_diagnostic_any_fallback(prop.value.span());
                  any_type_ann(self.allocator)
                }
              };

              members.push(TSSignature::TSPropertySignature(Box::new_in(
                TSPropertySignature::new(
                  SPAN,
                  computed,
                  false,
                  as_readonly,
                  key,
                  Some(init_type),
                  &AstBuilder::new(self.allocator),
                ),
                &self.allocator,
              )));
            }
            ObjectPropertyKind::SpreadProperty(spread) => {
              self.mark_diagnostic(
                FastCheckDtsDiagnostic::UnableToInferTypeFromSpread {
                  range: self.source_range_to_range(spread.span),
                },
              );
            }
          }
        }

        let mut oxc_members = Vec::new_in(&self.allocator);
        for m in members {
          oxc_members.push(m);
        }

        Some(TSType::TSTypeLiteral(Box::new_in(
          TSTypeLiteral::new(
            obj.span,
            oxc_members,
            &AstBuilder::new(self.allocator),
          ),
          &self.allocator,
        )))
      }
      Expression::BooleanLiteral(_)
      | Expression::NullLiteral(_)
      | Expression::NumericLiteral(_)
      | Expression::BigIntLiteral(_)
      | Expression::RegExpLiteral(_)
      | Expression::StringLiteral(_) => maybe_lit_to_ts_type(
        self.allocator,
        expr,
        match as_const {
          true => DeclMutabilityKind::Const,
          false => DeclMutabilityKind::Mutable,
        },
      ),
      Expression::TSAsExpression(ts_as) => {
        // Check if this is `as const` - OXC represents it as TSAsExpression
        // with type_annotation being TSTypeReference("const")
        if is_ts_const_type(&ts_as.type_annotation) {
          return self.expr_to_ts_type(&ts_as.expression, true, true);
        }
        Some(
          ts_as
            .type_annotation
            .clone_in_with_semantic_ids(self.allocator),
        )
      }
      Expression::TSSatisfiesExpression(satisfies) => {
        self.expr_to_ts_type(&satisfies.expression, as_const, as_readonly)
      }
      Expression::TSTypeAssertion(ts_assertion) => {
        // TsConstAssertion in SWC is TSTypeAssertion in OXC when
        // the type is "const". Check if it's `as const`.
        // Actually, OXC doesn't have a separate TsConstAssertion;
        // `as const` is represented as TSAsExpression with type TSTypeReference("const").
        // Let's just treat this as a type assertion and return the type.
        Some(
          ts_assertion
            .type_annotation
            .clone_in_with_semantic_ids(self.allocator),
        )
      }
      Expression::FunctionExpression(fn_expr) => {
        let return_type = fn_expr
          .return_type
          .as_ref()
          .map(|val| val.clone_in_with_semantic_ids(self.allocator))
          .unwrap_or_else(|| any_type_ann(self.allocator));

        let params = self.fn_params_to_ts_fn_params(&fn_expr.params);

        Some(TSType::TSFunctionType(Box::new_in(
          TSFunctionType::new(
            fn_expr.span,
            fn_expr
              .type_parameters
              .clone_in_with_semantic_ids(self.allocator),
            None,
            params,
            return_type,
            &AstBuilder::new(self.allocator),
          ),
          &self.allocator,
        )))
      }
      Expression::ArrowFunctionExpression(arrow_expr) => {
        let return_type = arrow_expr
          .return_type
          .as_ref()
          .map(|val| val.clone_in_with_semantic_ids(self.allocator))
          .unwrap_or_else(|| any_type_ann(self.allocator));

        let params = self.fn_params_to_ts_fn_params(&arrow_expr.params);

        Some(TSType::TSFunctionType(Box::new_in(
          TSFunctionType::new(
            arrow_expr.span,
            arrow_expr
              .type_parameters
              .clone_in_with_semantic_ids(self.allocator),
            None,
            params,
            return_type,
            &AstBuilder::new(self.allocator),
          ),
          &self.allocator,
        )))
      }
      Expression::TemplateLiteral(tpl) => Some(tpl_to_ts_type(
        self.allocator,
        tpl,
        match as_const {
          true => DeclMutabilityKind::Const,
          false => DeclMutabilityKind::Mutable,
        },
      )),
      Expression::Identifier(ident) => self.ident_to_ts_type(ident, as_const),
      Expression::UnaryExpression(unary) => {
        match (unary.operator, &unary.argument) {
          (
            UnaryOperator::UnaryNegation,
            Expression::NumericLiteral(_) | Expression::BigIntLiteral(_),
          ) => {
            if as_const {
              // `-1` is a valid literal type
              Some(TSType::new_ts_literal_type(
                unary.span,
                TSLiteral::UnaryExpression(Box::new_in(
                  unary.as_ref().clone_in_with_semantic_ids(self.allocator),
                  &self.allocator,
                )),
                &self.builder(),
              ))
            } else {
              let kind = match &unary.argument {
                Expression::NumericLiteral(_) => TSKeywordKind::Number,
                _ => TSKeywordKind::BigInt,
              };
              Some(ts_keyword_type(self.allocator, kind))
            }
          }
          _ => None,
        }
      }
      Expression::CallExpression(call_expr) => {
        // `Object.freeze(expr)` returns `Readonly<T>` of its argument
        let arg = object_freeze_call_arg(call_expr, self.scoping)?;
        let inner_type = self.expr_to_ts_type(arg, as_const, as_readonly)?;
        readonly_of(self.allocator, inner_type)
      }
      Expression::NewExpression(new_expr) => {
        // `new SomeClass(...)` of a non-generic class declared in this
        // module has the class instance type
        let Expression::Identifier(ident) = &new_expr.callee else {
          return None;
        };
        if new_expr.type_arguments.is_none()
          && self
            .non_generic_class_ids
            .contains(&ident.to_id(self.scoping))
        {
          Some(TSType::new_ts_type_reference(
            SPAN,
            TSTypeName::new_identifier_reference(
              SPAN,
              ident.name,
              &self.builder(),
            ),
            None,
            &self.builder(),
          ))
        } else {
          None
        }
      }
      // Since fast check requires explicit type annotations these
      // can be dropped as they are not part of an export declaration
      Expression::ThisExpression(_)
      | Expression::UpdateExpression(_)
      | Expression::BinaryExpression(_)
      | Expression::AssignmentExpression(_)
      | Expression::ConditionalExpression(_)
      | Expression::SequenceExpression(_)
      | Expression::TaggedTemplateExpression(_) => None,
      Expression::ClassExpression(class_expr) => {
        // Convert class expression to a type representing the class constructor.
        // Produces: { new(...): { members... }; } plus static members at top level.
        let body = self.class_body_to_type(&class_expr.body);

        // Build instance type from non-static, non-constructor members
        let mut instance_members: std::vec::Vec<TSSignature<'a>> =
          std::vec::Vec::new();
        for member in &body.body {
          match member {
            ClassElement::MethodDefinition(method) => {
              if method.r#static
                || method.kind == MethodDefinitionKind::Constructor
              {
                continue;
              }
              let kind = match method.kind {
                MethodDefinitionKind::Get => TSMethodSignatureKind::Get,
                MethodDefinitionKind::Set => TSMethodSignatureKind::Set,
                _ => TSMethodSignatureKind::Method,
              };
              instance_members.push(TSSignature::TSMethodSignature(
                Box::new_in(
                  TSMethodSignature::new(
                    SPAN,
                    method.key.clone_in_with_semantic_ids(self.allocator),
                    method.computed,
                    method.optional,
                    kind,
                    method
                      .value
                      .type_parameters
                      .clone_in_with_semantic_ids(self.allocator),
                    method
                      .value
                      .this_param
                      .clone_in_with_semantic_ids(self.allocator),
                    method
                      .value
                      .params
                      .clone_in_with_semantic_ids(self.allocator),
                    method
                      .value
                      .return_type
                      .clone_in_with_semantic_ids(self.allocator),
                    &AstBuilder::new(self.allocator),
                  ),
                  &self.allocator,
                ),
              ));
            }
            ClassElement::PropertyDefinition(prop) => {
              if prop.r#static {
                continue;
              }
              instance_members.push(TSSignature::TSPropertySignature(
                Box::new_in(
                  TSPropertySignature::new(
                    SPAN,
                    prop.computed,
                    prop.optional,
                    prop.readonly,
                    prop.key.clone_in_with_semantic_ids(self.allocator),
                    prop
                      .type_annotation
                      .clone_in_with_semantic_ids(self.allocator),
                    &AstBuilder::new(self.allocator),
                  ),
                  &self.allocator,
                ),
              ));
            }
            _ => {}
          }
        }

        // Build the instance type literal
        let mut oxc_instance_members = Vec::new_in(&self.allocator);
        for m in instance_members {
          oxc_instance_members.push(m);
        }
        let instance_type = TSType::TSTypeLiteral(Box::new_in(
          TSTypeLiteral::new(
            SPAN,
            oxc_instance_members,
            &AstBuilder::new(self.allocator),
          ),
          &self.allocator,
        ));

        // Find constructor params
        let ctor_params = body.body.iter().find_map(|m| {
          if let ClassElement::MethodDefinition(method) = m
            && method.kind == MethodDefinitionKind::Constructor
          {
            return Some(
              method
                .value
                .params
                .clone_in_with_semantic_ids(self.allocator),
            );
          }
          None
        });

        // Build: { new(...): InstanceType }
        let mut top_members = Vec::new_in(&self.allocator);
        top_members.push(TSSignature::TSConstructSignatureDeclaration(
          Box::new_in(
            TSConstructSignatureDeclaration::new(
              SPAN,
              class_expr
                .type_parameters
                .clone_in_with_semantic_ids(self.allocator),
              ctor_params.unwrap_or_else(|| {
                Box::new_in(
                  FormalParameters::new(
                    SPAN,
                    FormalParameterKind::Signature,
                    Vec::new_in(&self.allocator),
                    None,
                    &AstBuilder::new(self.allocator),
                  ),
                  &self.allocator,
                )
              }),
              Some(type_ann(self.allocator, instance_type)),
              &AstBuilder::new(self.allocator),
            ),
            &self.allocator,
          ),
        ));

        Some(TSType::TSTypeLiteral(Box::new_in(
          TSTypeLiteral::new(
            SPAN,
            top_members,
            &AstBuilder::new(self.allocator),
          ),
          &self.allocator,
        )))
      }
      Expression::YieldExpression(_)
      | Expression::ImportMeta(_)
      | Expression::NewTarget(_)
      | Expression::AwaitExpression(_)
      | Expression::ParenthesizedExpression(_)
      | Expression::JSXElement(_)
      | Expression::JSXFragment(_)
      | Expression::TSNonNullExpression(_)
      | Expression::TSInstantiationExpression(_)
      | Expression::PrivateInExpression(_)
      | Expression::Super(_)
      | Expression::LogicalExpression(_)
      | Expression::ImportExpression(_)
      | Expression::ChainExpression(_)
      | Expression::V8IntrinsicExpression(_)
      | Expression::ComputedMemberExpression(_)
      | Expression::StaticMemberExpression(_)
      | Expression::PrivateFieldExpression(_) => None,
    }
  }

  fn prop_key_to_expr_key(
    &self,
    key: &PropertyKey<'a>,
    computed: bool,
  ) -> (PropertyKey<'a>, bool) {
    match key {
      PropertyKey::StaticIdentifier(_)
      | PropertyKey::PrivateIdentifier(_)
      | PropertyKey::StringLiteral(_)
      | PropertyKey::NumericLiteral(_)
      | PropertyKey::BigIntLiteral(_) => {
        (key.clone_in_with_semantic_ids(self.allocator), computed)
      }
      _ => {
        // Expression variant - keep as computed
        (key.clone_in_with_semantic_ids(self.allocator), true)
      }
    }
  }

  fn decl_to_type_decl(
    &mut self,
    decl: Declaration<'a>,
  ) -> Option<Declaration<'a>> {
    let is_declare = self.is_top_level;
    match decl {
      Declaration::ClassDeclaration(mut class_decl) => {
        class_decl.body = self.class_body_to_type(&class_decl.body);
        class_decl.declare = is_declare;
        Some(Declaration::ClassDeclaration(class_decl))
      }
      Declaration::FunctionDeclaration(mut fn_decl) => {
        fn_decl.body = None;
        fn_decl.declare = is_declare;

        self.handle_func_params(&mut fn_decl.params);
        Some(Declaration::FunctionDeclaration(fn_decl))
      }
      Declaration::VariableDeclaration(mut var_decl) => {
        if matches!(
          var_decl.kind,
          VariableDeclarationKind::Using | VariableDeclarationKind::AwaitUsing
        ) {
          self.mark_diagnostic(FastCheckDtsDiagnostic::UnsupportedUsing {
            range: self.source_range_to_range(var_decl.span),
          });
          return None;
        }

        var_decl.declare = is_declare;

        for decl in var_decl.declarations.iter_mut() {
          if let BindingPattern::BindingIdentifier(ident) = &mut decl.id {
            if decl.type_annotation.is_some() {
              decl.init = None;
              continue;
            }

            let ts_type = decl
              .init
              .as_ref()
              .and_then(|init| self.expr_to_ts_type(init, false, true))
              .map(|t| type_ann(self.allocator, t))
              .or_else(|| {
                self.mark_diagnostic_any_fallback(ident.span);
                Some(any_type_ann(self.allocator))
              });
            decl.type_annotation = ts_type;
          } else {
            self.mark_diagnostic_unable_to_infer(decl.span);
          }

          decl.init = None;
        }

        Some(Declaration::VariableDeclaration(var_decl))
      }
      Declaration::TSEnumDeclaration(mut ts_enum) => {
        ts_enum.declare = is_declare;

        for member in ts_enum.body.members.iter_mut() {
          if let Some(init) = &member.initializer {
            // Support for expressions is limited in enums
            member.initializer = if self.valid_enum_init_expr(init) {
              Some(init.clone_in_with_semantic_ids(self.allocator))
            } else {
              None
            };
          }
        }

        Some(Declaration::TSEnumDeclaration(ts_enum))
      }
      Declaration::TSNamespaceDeclaration(mut ts_module) => {
        ts_module.declare = is_declare;
        self.transform_ts_ns_body(&mut ts_module.body);
        Some(Declaration::TSNamespaceDeclaration(ts_module))
      }
      Declaration::TSInterfaceDeclaration(_)
      | Declaration::TSTypeAliasDeclaration(_) => Some(decl),
      Declaration::TSGlobalDeclaration(_)
      | Declaration::TSExternalModuleDeclaration(_)
      | Declaration::TSImportEqualsDeclaration(_) => Some(decl),
    }
  }

  fn transform_ts_ns_body(&mut self, ns: &mut TSNamespaceDeclarationBody<'a>) {
    let original_is_top_level = self.is_top_level;
    self.is_top_level = false;
    match ns {
      TSNamespaceDeclarationBody::TSModuleBlock(ts_module_block) => {
        let stmts = std::mem::replace(
          &mut ts_module_block.body,
          Vec::new_in(&self.allocator),
        );
        ts_module_block.body = self.transform_stmts(stmts);
      }
      TSNamespaceDeclarationBody::TSNamespaceDeclaration(ts_ns) => {
        self.transform_ts_ns_body(&mut ts_ns.body);
      }
    }
    self.is_top_level = original_is_top_level;
  }

  // Support for expressions is limited in enums,
  // see https://www.typescriptlang.org/docs/handbook/enums.html
  fn valid_enum_init_expr(&mut self, expr: &Expression<'a>) -> bool {
    match expr {
      Expression::BinaryExpression(bin_expr) => {
        if !self.valid_enum_init_expr(&bin_expr.left) {
          false
        } else {
          self.valid_enum_init_expr(&bin_expr.right)
        }
      }
      Expression::StaticMemberExpression(member_expr) => {
        self.valid_enum_init_expr(&member_expr.object)
      }
      Expression::ComputedMemberExpression(member_expr) => {
        self.valid_enum_init_expr(&member_expr.object)
      }
      Expression::ChainExpression(chain_expr) => match &chain_expr.expression {
        ChainElement::StaticMemberExpression(member_expr) => {
          self.valid_enum_init_expr(&member_expr.object)
        }
        ChainElement::ComputedMemberExpression(member_expr) => {
          self.valid_enum_init_expr(&member_expr.object)
        }
        ChainElement::PrivateFieldExpression(member_expr) => {
          self.valid_enum_init_expr(&member_expr.object)
        }
        ChainElement::CallExpression(_)
        | ChainElement::TSNonNullExpression(_) => false,
      },
      // TS does infer the type of identifiers
      Expression::Identifier(_) => true,
      Expression::NumericLiteral(_) | Expression::StringLiteral(_) => true,
      Expression::BooleanLiteral(_)
      | Expression::NullLiteral(_)
      | Expression::BigIntLiteral(_)
      | Expression::RegExpLiteral(_) => false,
      Expression::TemplateLiteral(tpl_expr) => {
        for expr in &tpl_expr.expressions {
          if !self.valid_enum_init_expr(expr) {
            return false;
          }
        }
        true
      }
      Expression::ParenthesizedExpression(paren_expr) => {
        self.valid_enum_init_expr(&paren_expr.expression)
      }
      Expression::TSTypeAssertion(ts_ass) => {
        // Only assertions to number are allowed for computed
        // enum members.
        self.valid_enum_ts_type(&ts_ass.type_annotation)
      }
      Expression::TSAsExpression(ts_as) => {
        self.valid_enum_ts_type(&ts_as.type_annotation)
      }

      // These are not valid as enum member initializer
      Expression::TSInstantiationExpression(_)
      | Expression::CallExpression(_)
      | Expression::UpdateExpression(_)
      | Expression::PrivateInExpression(_)
      | Expression::TSSatisfiesExpression(_)
      | Expression::TSNonNullExpression(_)
      | Expression::ConditionalExpression(_)
      | Expression::SequenceExpression(_)
      | Expression::TaggedTemplateExpression(_)
      | Expression::ObjectExpression(_)
      | Expression::ArrayExpression(_)
      | Expression::ArrowFunctionExpression(_)
      | Expression::ClassExpression(_)
      | Expression::AwaitExpression(_)
      | Expression::ImportMeta(_)
      | Expression::NewTarget(_)
      | Expression::NewExpression(_)
      | Expression::JSXElement(_)
      | Expression::JSXFragment(_)
      | Expression::UnaryExpression(_)
      | Expression::AssignmentExpression(_)
      | Expression::YieldExpression(_)
      | Expression::Super(_)
      | Expression::FunctionExpression(_)
      | Expression::ThisExpression(_)
      | Expression::LogicalExpression(_)
      | Expression::ImportExpression(_)
      | Expression::V8IntrinsicExpression(_)
      | Expression::PrivateFieldExpression(_) => false,
    }
  }

  fn valid_enum_ts_type(&mut self, ts_type: &TSType<'a>) -> bool {
    match ts_type {
      TSType::TSLiteralType(ts_lit) => match &ts_lit.literal {
        TSLiteral::NumericLiteral(_) => true,
        TSLiteral::StringLiteral(_)
        | TSLiteral::BooleanLiteral(_)
        | TSLiteral::BigIntLiteral(_)
        | TSLiteral::TemplateLiteral(_)
        | TSLiteral::UnaryExpression(_) => false,
      },
      _ => false,
    }
  }

  fn ident_to_ts_type(
    &mut self,
    ident: &IdentifierReference<'a>,
    as_const: bool,
  ) -> Option<TSType<'a>> {
    let id = ident.to_id(self.scoping);
    if is_global_ident(ident, self.scoping) {
      return match ident.name.as_str() {
        "undefined" if as_const => {
          Some(TSType::new_ts_undefined_keyword(SPAN, &self.builder()))
        }
        "NaN" | "Infinity" => {
          Some(ts_keyword_type(self.allocator, TSKeywordKind::Number))
        }
        _ => None,
      };
    }
    if self.typeof_safe_ids.contains(&id) {
      Some(TSType::new_ts_type_query(
        SPAN,
        TSTypeQueryExprName::new_identifier_reference(
          SPAN,
          ident.name,
          &self.builder(),
        ),
        None,
        &self.builder(),
      ))
    } else {
      None
    }
  }

  fn infer_expr_fallback_any(
    &mut self,
    expr: &Expression<'a>,
    as_const: bool,
    as_readonly: bool,
  ) -> Box<'a, TSTypeAnnotation<'a>> {
    match self.expr_to_ts_type(expr, as_const, as_readonly) {
      Some(ts_type) => type_ann(self.allocator, ts_type),
      _ => {
        self.mark_diagnostic_any_fallback(expr.span());
        any_type_ann(self.allocator)
      }
    }
  }

  fn class_body_to_type(
    &mut self,
    body: &Box<'a, ClassBody<'a>>,
  ) -> Box<'a, ClassBody<'a>> {
    let filtered: std::vec::Vec<ClassElement<'a>> = body
      .body
      .clone_in_with_semantic_ids(self.allocator)
      .into_iter()
      .filter(|member| match member {
        ClassElement::MethodDefinition(method) => {
          !self.public_ranges.is_impl_with_overloads(&method.span)
        }
        ClassElement::TSIndexSignature(_)
        | ClassElement::PropertyDefinition(_)
        | ClassElement::StaticBlock(_)
        | ClassElement::AccessorProperty(_) => true,
      })
      .filter_map(|member| match member {
        ClassElement::MethodDefinition(mut method) => {
          // Skip private methods (PrivateIdentifier / #name)
          if let PropertyKey::PrivateIdentifier(_) = &method.key {
            return None;
          }

          if method.kind == MethodDefinitionKind::Constructor {
            // Constructor
            method.value.body = None;
            self.handle_func_params(&mut method.value.params);
            Some(ClassElement::MethodDefinition(method))
          } else {
            // Regular method / getter / setter
            match valid_prop_name(self.allocator, self.scoping, &method.key) {
              Some(new_prop_name) => {
                method.key = new_prop_name;
              }
              _ => {
                return None;
              }
            }

            method.value.body = None;
            if method.kind == MethodDefinitionKind::Set {
              method.value.return_type = None;
            }
            self.handle_func_params(&mut method.value.params);
            Some(ClassElement::MethodDefinition(method))
          }
        }
        ClassElement::PropertyDefinition(mut prop) => {
          // Skip private properties (PrivateIdentifier)
          if let PropertyKey::PrivateIdentifier(_) = &prop.key {
            return None;
          }

          match valid_prop_name(self.allocator, self.scoping, &prop.key) {
            Some(new_prop_name) => {
              prop.key = new_prop_name;
            }
            _ => {
              return None;
            }
          }
          if prop.type_annotation.is_none()
            && let Some(ref value) = prop.value
          {
            prop.type_annotation = self
              .expr_to_ts_type(value, false, false)
              .map(|t| type_ann(self.allocator, t))
              .or_else(|| Some(any_type_ann(self.allocator)));
          }
          prop.value = None;
          prop.definite = false;
          prop.declare = false;

          Some(ClassElement::PropertyDefinition(prop))
        }
        ClassElement::TSIndexSignature(index_sig) => {
          Some(ClassElement::TSIndexSignature(index_sig))
        }

        // These can be removed as they are not relevant for types
        ClassElement::StaticBlock(_) | ClassElement::AccessorProperty(_) => {
          None
        }
      })
      .collect();

    let mut oxc_body = Vec::new_in(&self.allocator);
    for el in filtered {
      oxc_body.push(el);
    }

    Box::new_in(
      ClassBody::new(body.span, oxc_body, &AstBuilder::new(self.allocator)),
      &self.allocator,
    )
  }

  fn handle_func_params(&mut self, params: &mut Box<'a, FormalParameters<'a>>) {
    for param in params.items.iter_mut() {
      self.handle_func_param(param);
    }
  }

  fn handle_func_param(&mut self, param: &mut FormalParameter<'a>) {
    // In OXC, parameter defaults are stored in FormalParameter::initializer
    // (not as AssignmentPattern in the pattern field).
    if let Some(init) = param.initializer.take() {
      // Has a default value: infer type if missing, make optional, remove default
      if param.type_annotation.is_none() {
        param.type_annotation =
          Some(self.infer_expr_fallback_any(&init, false, false));
      }
      param.optional = true;
      // initializer already taken via take()
      return;
    }

    match &mut param.pattern {
      BindingPattern::BindingIdentifier(ident) => {
        if param.type_annotation.is_none() {
          self.mark_diagnostic_any_fallback(ident.span);
          param.type_annotation = Some(any_type_ann(self.allocator));
        }
      }
      BindingPattern::AssignmentPattern(assign_pat) => {
        if let Some(new_result) =
          self.handle_func_param_assign(assign_pat, &mut param.type_annotation)
        {
          param.pattern = new_result;
          param.optional = true;
        }
      }
      BindingPattern::ArrayPattern(_) | BindingPattern::ObjectPattern(_) => {}
    }
  }

  fn handle_func_param_assign(
    &mut self,
    assign_pat: &mut AssignmentPattern<'a>,
    param_type_annotation: &mut Option<Box<'a, TSTypeAnnotation<'a>>>,
  ) -> Option<BindingPattern<'a>> {
    match &mut assign_pat.left {
      BindingPattern::BindingIdentifier(ident) => {
        if param_type_annotation.is_none() {
          *param_type_annotation =
            Some(self.infer_expr_fallback_any(&assign_pat.right, false, false));
        }

        Some(BindingPattern::BindingIdentifier(
          ident.clone_in_with_semantic_ids(self.allocator),
        ))
      }
      BindingPattern::ArrayPattern(arr_pat) => {
        if param_type_annotation.is_none() {
          *param_type_annotation =
            Some(self.infer_expr_fallback_any(&assign_pat.right, false, false));
        }

        Some(BindingPattern::ArrayPattern(
          arr_pat.clone_in_with_semantic_ids(self.allocator),
        ))
      }
      BindingPattern::ObjectPattern(obj_pat) => {
        if param_type_annotation.is_none() {
          *param_type_annotation =
            Some(self.infer_expr_fallback_any(&assign_pat.right, false, false));
        }

        Some(BindingPattern::ObjectPattern(
          obj_pat.clone_in_with_semantic_ids(self.allocator),
        ))
      }
      BindingPattern::AssignmentPattern(_) => None,
    }
  }

  fn fn_params_to_ts_fn_params(
    &mut self,
    params: &FormalParameters<'a>,
  ) -> Box<'a, FormalParameters<'a>> {
    let mut items = Vec::new_in(&self.allocator);
    for param in &params.items {
      if let Some(fp) = self.param_to_ts_fn_param(param) {
        items.push(fp);
      }
    }
    let rest = params.rest.clone_in_with_semantic_ids(self.allocator);
    Box::new_in(
      FormalParameters::new(
        params.span,
        FormalParameterKind::Signature,
        items,
        rest,
        &AstBuilder::new(self.allocator),
      ),
      &self.allocator,
    )
  }

  fn param_to_ts_fn_param(
    &mut self,
    param: &FormalParameter<'a>,
  ) -> Option<FormalParameter<'a>> {
    // In OXC, parameter defaults are in FormalParameter::initializer
    if let Some(init) = &param.initializer {
      let ta = param
        .type_annotation
        .clone_in_with_semantic_ids(self.allocator)
        .or_else(|| {
          self
            .expr_to_ts_type(init, false, false)
            .map(|t| type_ann(self.allocator, t))
        });
      return Some(FormalParameter::new(
        param.span,
        Vec::new_in(&self.allocator),
        param.pattern.clone_in_with_semantic_ids(self.allocator),
        ta,
        None,
        false,
        param.accessibility,
        param.readonly,
        param.r#override,
        &AstBuilder::new(self.allocator),
      ));
    }

    match &param.pattern {
      BindingPattern::BindingIdentifier(binding_id) => {
        Some(FormalParameter::new(
          param.span,
          Vec::new_in(&self.allocator),
          BindingPattern::BindingIdentifier(
            binding_id.clone_in_with_semantic_ids(self.allocator),
          ),
          param
            .type_annotation
            .clone_in_with_semantic_ids(self.allocator),
          None,
          param.optional,
          param.accessibility,
          param.readonly,
          param.r#override,
          &AstBuilder::new(self.allocator),
        ))
      }
      BindingPattern::ArrayPattern(_) => {
        Some(param.clone_in_with_semantic_ids(self.allocator))
      }
      BindingPattern::ObjectPattern(_) => {
        Some(param.clone_in_with_semantic_ids(self.allocator))
      }
      BindingPattern::AssignmentPattern(assign_pat) => self
        .expr_to_ts_type(&assign_pat.right, false, false)
        .map(|ts_type| {
          let name = if let BindingPattern::BindingIdentifier(ident) =
            &assign_pat.left
          {
            ident.name
          } else {
            Ident::from(self.allocator.alloc_str(&self.gen_unique_name()))
          };

          FormalParameter::new(
            assign_pat.span,
            Vec::new_in(&self.allocator),
            BindingPattern::BindingIdentifier(Box::new_in(
              BindingIdentifier::new(
                assign_pat.span,
                name,
                &AstBuilder::new(self.allocator),
              ),
              &self.allocator,
            )),
            Some(type_ann(self.allocator, ts_type)),
            None,
            false,
            None,
            false,
            false,
            &AstBuilder::new(self.allocator),
          )
        }),
    }
  }
}

/// Check if a TSType is the `const` type reference used in `as const`.
fn is_ts_const_type(ty: &TSType) -> bool {
  if let TSType::TSTypeReference(type_ref) = ty
    && let TSTypeName::IdentifierReference(ident) = &type_ref.type_name
  {
    return ident.name.as_str() == "const";
  }
  false
}

#[derive(Default)]
struct PrescannedModuleIds {
  /// Bindings whose type can be soundly referenced via `typeof` in the
  /// emitted declaration file: function and class declarations don't get
  /// widened by TypeScript's inference, and consts with an explicit type
  /// annotation or a function initializer have a known non-widening
  /// declared type.
  typeof_safe: HashSet<Id>,
  /// Class declarations without type parameters.
  non_generic_classes: HashSet<Id>,
  /// Bindings with an array or tuple type, per their type annotation or an
  /// array literal initializer.
  array_typed: HashSet<Id>,
}

/// The equivalent of `Readonly<T>`, expressed without referencing the
/// global `Readonly` utility type since that identifier could be shadowed
/// by a module-local type declaration. Types that can't be represented
/// structurally return `None`.
fn readonly_of<'a>(
  allocator: &'a Allocator,
  ts_type: TSType<'a>,
) -> Option<TSType<'a>> {
  match ts_type {
    TSType::TSTypeLiteral(mut type_lit)
      if type_lit.members.iter().all(|member| {
        matches!(
          member,
          TSSignature::TSPropertySignature(_)
            | TSSignature::TSIndexSignature(_)
        )
      }) =>
    {
      for member in type_lit.members.iter_mut() {
        match member {
          TSSignature::TSPropertySignature(prop) => prop.readonly = true,
          TSSignature::TSIndexSignature(index) => index.readonly = true,
          _ => unreachable!(),
        }
      }
      Some(TSType::TSTypeLiteral(type_lit))
    }
    TSType::TSArrayType(_) | TSType::TSTupleType(_) => {
      Some(ts_readonly(allocator, ts_type))
    }
    TSType::TSTypeOperatorType(op)
      if op.operator == TSTypeOperatorOperator::Readonly =>
    {
      Some(TSType::TSTypeOperatorType(op))
    }
    // `Object.freeze` returns functions unchanged
    TSType::TSFunctionType(_) => Some(ts_type),
    _ => None,
  }
}

fn is_array_type(ty: &TSType) -> bool {
  match ty {
    TSType::TSArrayType(_) | TSType::TSTupleType(_) => true,
    TSType::TSTypeOperatorType(op)
      if op.operator == TSTypeOperatorOperator::Readonly =>
    {
      is_array_type(&op.type_annotation)
    }
    TSType::TSTypeReference(type_ref) => matches!(
      &type_ref.type_name,
      TSTypeName::IdentifierReference(ident)
        if ident.name == "Array" || ident.name == "ReadonlyArray"
    ),
    _ => false,
  }
}

fn is_array_lit_init(expr: &Expression) -> bool {
  match expr {
    Expression::ArrayExpression(_) => true,
    Expression::ParenthesizedExpression(e) => is_array_lit_init(&e.expression),
    Expression::TSSatisfiesExpression(e) => is_array_lit_init(&e.expression),
    Expression::TSAsExpression(e) => {
      if is_ts_const_type(&e.type_annotation) {
        is_array_lit_init(&e.expression)
      } else {
        is_array_type(&e.type_annotation)
      }
    }
    _ => false,
  }
}

fn prescan_module_ids(
  program: &Program,
  scoping: Option<&Scoping>,
) -> PrescannedModuleIds {
  fn add_class(
    ids: &mut PrescannedModuleIds,
    scoping: Option<&Scoping>,
    ident: &BindingIdentifier,
    class: &Class,
  ) {
    ids.typeof_safe.insert(ident.to_id(scoping));
    if class.type_parameters.is_none() {
      ids.non_generic_classes.insert(ident.to_id(scoping));
    }
  }

  fn add_decl(
    ids: &mut PrescannedModuleIds,
    scoping: Option<&Scoping>,
    decl: &Declaration,
  ) {
    match decl {
      Declaration::FunctionDeclaration(n) => {
        if let Some(ident) = &n.id {
          ids.typeof_safe.insert(ident.to_id(scoping));
        }
      }
      Declaration::ClassDeclaration(n) => {
        if let Some(ident) = &n.id {
          add_class(ids, scoping, ident, n);
        }
      }
      Declaration::VariableDeclaration(n)
        if n.kind == VariableDeclarationKind::Const =>
      {
        for declarator in &n.declarations {
          if let BindingPattern::BindingIdentifier(ident) = &declarator.id {
            let is_typed = declarator.type_annotation.is_some();
            let has_fn_init = matches!(
              declarator.init,
              Some(
                Expression::FunctionExpression(_)
                  | Expression::ArrowFunctionExpression(_)
              )
            );
            if is_typed || has_fn_init {
              ids.typeof_safe.insert(ident.to_id(scoping));
            }
            let is_array_typed = match &declarator.type_annotation {
              Some(type_ann) => is_array_type(&type_ann.type_annotation),
              None => declarator.init.as_ref().is_some_and(is_array_lit_init),
            };
            if is_array_typed {
              ids.array_typed.insert(ident.to_id(scoping));
            }
          }
        }
      }
      _ => {}
    }
  }

  let mut ids = PrescannedModuleIds::default();
  for stmt in &program.body {
    match stmt {
      Statement::ExportDeclaration(n) => {
        add_decl(&mut ids, scoping, &n.declaration)
      }
      Statement::ExportDefaultDeclaration(n) => match &n.declaration {
        ExportDefaultDeclarationKind::ClassDeclaration(class) => {
          if let Some(ident) = &class.id {
            add_class(&mut ids, scoping, ident, class);
          }
        }
        ExportDefaultDeclarationKind::FunctionDeclaration(func) => {
          if let Some(ident) = &func.id {
            ids.typeof_safe.insert(ident.to_id(scoping));
          }
        }
        _ => {}
      },
      stmt => {
        if let Some(decl) = stmt.as_declaration() {
          add_decl(&mut ids, scoping, decl);
        }
      }
    }
  }
  ids
}

/// Whether the expression is a reference to a well-known symbol on the
/// global `Symbol` object (e.g. `Symbol.iterator` or `Symbol.dispose`).
fn is_well_known_symbol_expr(
  expr: &Expression,
  scoping: Option<&Scoping>,
) -> bool {
  const WELL_KNOWN_SYMBOL_NAMES: [&str; 16] = [
    "asyncDispose",
    "asyncIterator",
    "dispose",
    "hasInstance",
    "isConcatSpreadable",
    "iterator",
    "match",
    "matchAll",
    "metadata",
    "replace",
    "search",
    "species",
    "split",
    "toPrimitive",
    "toStringTag",
    "unscopables",
  ];

  let Expression::StaticMemberExpression(member_expr) = expr else {
    return false;
  };
  let Expression::Identifier(obj_ident) = &member_expr.object else {
    return false;
  };
  if obj_ident.name != "Symbol" || !is_global_ident(obj_ident, scoping) {
    return false;
  }
  WELL_KNOWN_SYMBOL_NAMES.contains(&member_expr.property.name.as_str())
}

fn valid_prop_name<'a>(
  allocator: &'a Allocator,
  scoping: Option<&Scoping>,
  prop_key: &PropertyKey<'a>,
) -> Option<PropertyKey<'a>> {
  fn prop_name_from_property_key<'a>(
    allocator: &'a Allocator,
    scoping: Option<&Scoping>,
    key: &PropertyKey<'a>,
  ) -> Option<PropertyKey<'a>> {
    match key {
      PropertyKey::StaticIdentifier(_) => {
        Some(key.clone_in_with_semantic_ids(allocator))
      }
      PropertyKey::PrivateIdentifier(_) => {
        Some(key.clone_in_with_semantic_ids(allocator))
      }
      // Expression variants
      PropertyKey::StringLiteral(_)
      | PropertyKey::NumericLiteral(_)
      | PropertyKey::BigIntLiteral(_) => {
        Some(key.clone_in_with_semantic_ids(allocator))
      }
      PropertyKey::TemplateLiteral(tpl) => {
        if tpl.quasis.is_empty() && tpl.expressions.len() == 1 {
          prop_name_from_expr(allocator, scoping, &tpl.expressions[0])
        } else {
          None
        }
      }
      PropertyKey::ParenthesizedExpression(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      PropertyKey::TSTypeAssertion(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      PropertyKey::TSNonNullExpression(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      PropertyKey::TSAsExpression(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      PropertyKey::TSSatisfiesExpression(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      PropertyKey::Identifier(_ident) => {
        // Computed identifier - keep as computed property key
        Some(key.clone_in_with_semantic_ids(allocator))
      }
      PropertyKey::StaticMemberExpression(_) => {
        // `[Symbol.iterator]` and friends
        let expr = key.as_expression()?;
        if is_well_known_symbol_expr(expr, scoping) {
          Some(key.clone_in_with_semantic_ids(allocator))
        } else {
          None
        }
      }
      _ => None,
    }
  }

  fn prop_name_from_expr<'a>(
    allocator: &'a Allocator,
    scoping: Option<&Scoping>,
    expr: &Expression<'a>,
  ) -> Option<PropertyKey<'a>> {
    match expr {
      Expression::StringLiteral(s) => Some(PropertyKey::StringLiteral(
        s.clone_in_with_semantic_ids(allocator),
      )),
      Expression::NumericLiteral(n) => Some(PropertyKey::NumericLiteral(
        n.clone_in_with_semantic_ids(allocator),
      )),
      Expression::BigIntLiteral(b) => Some(PropertyKey::BigIntLiteral(
        b.clone_in_with_semantic_ids(allocator),
      )),
      Expression::TemplateLiteral(e) => {
        if e.quasis.is_empty() && e.expressions.len() == 1 {
          prop_name_from_expr(allocator, scoping, &e.expressions[0])
        } else {
          None
        }
      }
      Expression::ParenthesizedExpression(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      Expression::TSTypeAssertion(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      Expression::TSNonNullExpression(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      Expression::TSAsExpression(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      Expression::TSSatisfiesExpression(e) => {
        prop_name_from_expr(allocator, scoping, &e.expression)
      }
      Expression::Identifier(id) => {
        // Computed identifier reference
        Some(PropertyKey::new_identifier(
          id.span,
          id.name,
          &AstBuilder::new(allocator),
        ))
      }
      Expression::StaticMemberExpression(_) => {
        if is_well_known_symbol_expr(expr, scoping) {
          Some(PropertyKey::from(
            expr.clone_in_with_semantic_ids(allocator),
          ))
        } else {
          None
        }
      }
      _ => None,
    }
  }

  prop_name_from_property_key(allocator, scoping, prop_key)
}

#[cfg(test)]
mod tests {
  use std::collections::VecDeque;

  use crate::BuildOptions;
  use crate::GraphKind;
  use crate::ModuleGraph;
  use crate::WorkspaceMember;
  use crate::ast::CapturingModuleAnalyzer;
  use crate::ast::EsParser;
  use crate::fast_check::range_finder::find_public_ranges;
  use crate::fast_check::transform_dts::FastCheckDtsTransformer;
  use crate::source::MemoryLoader;
  use crate::source::Source;
  use crate::symbols::RootSymbol;
  use deno_ast::EmitOptions;
  use deno_ast::EmittedSourceText;
  use deno_ast::ModuleSpecifier;
  use deno_ast::emit;
  use deno_ast::oxc::allocator::CloneIn;
  use deno_semver::package::PackageNv;
  use indexmap::IndexMap;
  use url::Url;

  async fn transform_dts_test(source: &str, expected: &str) {
    let specifier = Url::parse("file:///mod.ts").unwrap();

    let loader = MemoryLoader::new(
      vec![(
        specifier.to_string(),
        Source::Module {
          specifier: specifier.to_string(),
          maybe_headers: None,
          content: source.to_string(),
        },
      )],
      vec![],
    );
    let analyzer = CapturingModuleAnalyzer::default();
    let allocator = deno_ast::oxc::allocator::Allocator::default();
    let mut graph = ModuleGraph::new(GraphKind::All);
    graph
      .build(
        vec![specifier.clone()],
        Default::default(),
        &loader,
        BuildOptions {
          module_analyzer: &analyzer,
          ..Default::default()
        },
      )
      .await;

    let root_sym = RootSymbol::new(&graph, &analyzer, &allocator);

    let _module_info = root_sym
      .module_from_specifier(&specifier)
      .unwrap()
      .esm()
      .unwrap();

    let parsed_source = analyzer
      .parse_program(
        &allocator,
        crate::ast::ParseOptions {
          specifier: &specifier,
          source: source.into(),
          media_type: deno_ast::MediaType::TypeScript,
          scope_analysis: true,
        },
      )
      .unwrap();
    let program = parsed_source
      .program()
      .clone_in_with_semantic_ids(&allocator);
    let nv = PackageNv::from_str("package@1.0.0").unwrap();
    let public_ranges = find_public_ranges(
      None,
      Default::default(),
      &graph,
      &root_sym,
      &[WorkspaceMember {
        base: ModuleSpecifier::parse("file:///").unwrap(),
        name: nv.name.clone(),
        version: Some(nv.version.clone()),
        exports: IndexMap::from([(".".to_string(), "./mod.ts".to_string())]),
      }],
      VecDeque::from([nv.clone()]),
    )
    .remove(&nv)
    .unwrap()
    .module_ranges
    .shift_remove(&specifier)
    .unwrap();

    let mut transformer = FastCheckDtsTransformer::new(
      &allocator,
      parsed_source.text_info_lazy(),
      &public_ranges,
      &specifier,
      parsed_source.scoping(),
    );
    let program = transformer.transform(program);

    let EmittedSourceText { text: actual, .. } = emit(
      &program,
      parsed_source.text(),
      specifier.as_ref(),
      &EmitOptions {
        remove_comments: false,
        source_map: deno_ast::SourceMapOption::None,
        source_map_base: None,
        source_map_file: None,
        inline_sources: false,
        ascii_only: false,
      },
    )
    .unwrap();

    assert_eq!(actual.trim(), expected.trim());
  }

  #[tokio::test]
  async fn dts_function_test() {
    transform_dts_test(
      r#"export function foo(a: number): number {
  return {};
}"#,
      "export declare function foo(a: number): number;",
    )
    .await;
    transform_dts_test(
      r#"export function foo(a: string): number;
export function foo(a: any): number {
  return {};
}"#,
      r#"export declare function foo(a: string): number;"#,
    )
    .await;
    transform_dts_test(
      r#"export function foo(a = 2): number {
  return 2;
}"#,
      r#"export declare function foo(a?: number): number;"#,
    )
    .await;
    transform_dts_test(
      r#"export function foo(a: string = 2): number {
  return 2;
}"#,
      r#"export declare function foo(a?: string): number;"#,
    )
    .await;
    transform_dts_test(
      r#"export function foo([a, b] = [1, 2]): number {
  return 2;
}"#,
      r#"export declare function foo([a, b]?: [number, number]): number;"#,
    )
    .await;
    transform_dts_test(
      r#"export function foo({a, b} = { a: 1, b: 2 }): number {
  return 2;
}"#,
      r#"export declare function foo({ a, b }?: {
  a: number;
  b: number;
}): number;"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_class_decl_test() {
    transform_dts_test(
      r#"export class Foo {
  a: number = 2;
  static b: number = 1;
  #b: number = 3;
  constructor(value: string) {
    return 42;
  }
  foo(): string {
    return "abc";
  }
  #bar(): number {
    return 2
  }
  get asdf(): number {

  }
  set asdf(value: number) {

  }

  static {

  }
}"#,
      r#"export declare class Foo {
  a: number;
  static b: number;
  constructor(value: string);
  foo(): string;
  get asdf(): number;
  set asdf(value: number);
}"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_class_decl_rest_test() {
    transform_dts_test(
      r#"export class Foo {
  constructor(...args: string[]) {}
}"#,
      r#"export declare class Foo {
  constructor(...args: string[]);
}"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_class_decl_overloads_test() {
    transform_dts_test(
      r#"export class Foo {
  constructor(arg: string);
  constructor(arg: number);
  constructor(arg: any) {}
}"#,
      r#"export declare class Foo {
  constructor(arg: string);
  constructor(arg: number);
}"#,
    )
    .await;

    transform_dts_test(
      r#"export class Foo {
  foo(arg: string);
  foo(arg: number);
  foo(arg: any) {}
}"#,
      r#"export declare class Foo {
  foo(arg: string);
  foo(arg: number);
}"#,
    )
    .await;

    transform_dts_test(
      r#"export class Foo {
  constructor(arg: string);
  constructor(arg: number);
  constructor(arg: any) {}

  bar(arg: number): number {
    return 2
  }

  foo(arg: string);
  foo(arg: number);
  foo(arg: any) {}
}"#,
      r#"export declare class Foo {
  constructor(arg: string);
  constructor(arg: number);
  bar(arg: number): number;
  foo(arg: string);
  foo(arg: number);
}"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_class_decl_prop_test() {
    transform_dts_test(
      r#"export class Foo { private a!: string }"#,
      r#"export declare class Foo {
  private a: string;
}"#,
    )
    .await;

    transform_dts_test(
      r#"export class Foo { declare a: string }"#,
      r#"export declare class Foo {
  a: string;
}"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_class_decl_prop_infer_test() {
    transform_dts_test(
      r#"export class Foo { foo = (a: string): string => ({} as any) }"#,
      r#"export declare class Foo {
  foo: (a: string) => string;
}"#,
    )
    .await;
    transform_dts_test(
      r#"export class Foo { foo = function(a: string): void {} }"#,
      r#"export declare class Foo {
  foo: (a: string) => void;
}"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_var_decl_test() {
    transform_dts_test(
      r#"export const foo: number = 42;"#,
      "export declare const foo: number;",
    )
    .await;

    transform_dts_test(
      r#"export var foo: number = 42;"#,
      "export declare var foo: number;",
    )
    .await;

    transform_dts_test(
      r#"export let foo: number = 42;"#,
      "export declare let foo: number;",
    )
    .await;

    // Default to any if it cannot be determined
    transform_dts_test(
      r#"export const foo = adsf.b;"#,
      "export declare const foo: any;",
    )
    .await;
    transform_dts_test(r#"export let foo;"#, "export declare let foo: any;")
      .await;
  }

  #[tokio::test]
  async fn dts_global_declare() {
    transform_dts_test(
      r#"declare global {
  interface String {
    fancyFormat(opts: StringFormatOptions): string;
  }
}"#,
      r#"declare global {
  interface String {
    fancyFormat(opts: StringFormatOptions): string;
  }
}"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_inference() {
    transform_dts_test(
      r#"export const foo = null as string as number;"#,
      "export declare const foo: number;",
    )
    .await;
  }

  #[tokio::test]
  async fn dts_as_const() {
    transform_dts_test(
      r#"export const foo = [1, 2] as const;"#,
      "export declare const foo: readonly [1, 2];",
    )
    .await;
    transform_dts_test(
      r#"export const foo = [1, ,2] as const;"#,
      "export declare const foo: readonly [1, any, 2];",
    )
    .await;

    transform_dts_test(
      r#"export const foo = { str: "bar", bool: true, bool2: false, num: 42,   nullish: null } as const;"#,
      r#"export declare const foo: {
  readonly str: "bar";
  readonly bool: true;
  readonly bool2: false;
  readonly num: 42;
  readonly nullish: null;
};"#,
    ).await;

    transform_dts_test(
      r#"export const foo = { str: [1, 2] as const } as const;"#,
      r#"export declare const foo: {
  readonly str: readonly [1, 2];
};"#,
    )
    .await;

    // TODO: Requires type resolving
    transform_dts_test(
      r#"export const foo = { bar } as const;"#,
      r#"export declare const foo: {};"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_object_prop_ident_reference() {
    // https://github.com/jsr-io/jsr/issues/615
    transform_dts_test(
      r#"export function fAdd(a: number, b: number): number {
  return a + b;
}
export class Foo {}
const arrow = (a: string): string => a;
const typed: number = 1;
export const obj = {
  add: fAdd,
  arrow,
  klass: Foo,
  typed,
};"#,
      r#"export declare function fAdd(a: number, b: number): number;
export declare class Foo {}
declare const arrow: (a: string) => string;
declare const typed: number;
export declare const obj: {
  readonly add: typeof fAdd;
  readonly arrow: typeof arrow;
  readonly klass: typeof Foo;
  readonly typed: typeof typed;
};"#,
    )
    .await;

    // a `let` variable may be widened by TypeScript's inference, so
    // referencing it via `typeof` is not safe and falls back to `any`
    transform_dts_test(
      r#"let counter = 0;
export const obj = { counter };"#,
      r#"declare let counter: number;
export declare const obj: {};"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_ident_globals() {
    transform_dts_test(
      r#"export const foo = { u: undefined, n: NaN, i: Infinity } as const;"#,
      r#"export declare const foo: {
  readonly u: undefined;
  readonly n: number;
  readonly i: number;
};"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_class_wellknown_symbol_members() {
    // https://github.com/jsr-io/jsr/issues/886
    // https://github.com/jsr-io/jsr/issues/1179
    transform_dts_test(
      r#"export class Foo<T> implements Iterable<T> {
  [Symbol.iterator](): Iterator<T> {
    return null!;
  }
  [Symbol.dispose](): void {}
  readonly [Symbol.toStringTag]: string = "Foo";
}"#,
      r#"export declare class Foo<T> implements Iterable<T> {
  [Symbol.iterator](): Iterator<T>;
  [Symbol.dispose](): void;
  readonly [Symbol.toStringTag]: string;
}"#,
    )
    .await;

    // a local binding named `Symbol` is not the global `Symbol` object
    transform_dts_test(
      r#"const Symbol = { iterator: "iter" } as const;
export class Foo {
  [Symbol.iterator](): void {}
}"#,
      r#"declare const Symbol: {
  readonly iterator: "iter";
};
export declare class Foo {}"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_as_const_spread() {
    // https://github.com/jsr-io/jsr/issues/1258
    transform_dts_test(
      r#"export const FIRST = ["a", "b"] as const;
export const ALL = [...FIRST, "c", "d"] as const;"#,
      r#"export declare const FIRST: readonly ["a", "b"];
export declare const ALL: readonly [...typeof FIRST, "c", "d"];"#,
    )
    .await;

    transform_dts_test(
      r#"export const flat = [...[1, 2], ...["test"]] as const;"#,
      "export declare const flat: readonly [...[1, 2], ...[\"test\"]];",
    )
    .await;

    // a spread of an uninferable expression falls back to `any` for the
    // whole array instead of emitting a tuple with missing elements
    transform_dts_test(
      r#"export const nope = [...foo(), "a"] as const;"#,
      "export declare const nope: any;",
    )
    .await;

    // a spread of a binding that is not array-typed cannot become a tuple
    // rest element (`...typeof source` of a string is invalid TypeScript)
    transform_dts_test(
      r#"const source: string = "abc";
export const bad = [...source, "a"] as const;"#,
      r#"declare const source: string;
export declare const bad: any;"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_negative_number_literals() {
    transform_dts_test(
      r#"export const nums = [1, -2, 3.5] as const;"#,
      "export declare const nums: readonly [1, -2, 3.5];",
    )
    .await;
  }

  #[tokio::test]
  async fn dts_new_expr() {
    transform_dts_test(
      r#"export class Dimensions {}
export const a = { d: new Dimensions() };"#,
      r#"export declare class Dimensions {}
export declare const a: {
  readonly d: Dimensions;
};"#,
    )
    .await;

    // generic classes are not inferable from a `new` expression
    transform_dts_test(
      r#"export class Box<T> {}
export const a = new Box("test");"#,
      r#"export declare class Box<T> {}
export declare const a: any;"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_object_freeze() {
    // https://github.com/jsr-io/jsr/issues/155
    transform_dts_test(
      r#"export const props = Object.freeze({ a: 1, b: "test" });"#,
      r#"export declare const props: {
  readonly a: number;
  readonly b: string;
};"#,
    )
    .await;

    transform_dts_test(
      r#"export const list = Object.freeze([1, 2]);"#,
      "export declare const list: readonly [number, number];",
    )
    .await;

    // the emitted type must not reference the global `Readonly` utility
    // type, which can be shadowed by a module-local declaration
    transform_dts_test(
      r#"export type Readonly<T> = string;
export const frozen = Object.freeze({ value: 1 });"#,
      r#"export type Readonly<T> = string;
export declare const frozen: {
  readonly value: number;
};"#,
    )
    .await;

    // other calls are still not inferable
    transform_dts_test(
      r#"export const foo = Object.entries({ a: 1 });"#,
      "export declare const foo: any;",
    )
    .await;
  }

  #[tokio::test]
  async fn dts_literal_inference_ann() {
    transform_dts_test(
      r#"export const foo: number = "abc";"#,
      "export declare const foo: number;",
    )
    .await;
    transform_dts_test(
      r#"export let foo: number = "abc";"#,
      "export declare let foo: number;",
    )
    .await;
    transform_dts_test(
      r#"export var foo: number = "abc";"#,
      "export declare var foo: number;",
    )
    .await;
  }

  #[tokio::test]
  async fn dts_literal_inference() {
    transform_dts_test(
      r#"export const foo = 42;"#,
      "export declare const foo: number;",
    )
    .await;
    transform_dts_test(
      r#"export const foo = "foo";"#,
      "export declare const foo: string;",
    )
    .await;
    transform_dts_test(
      r#"export const foo = true;"#,
      "export declare const foo: boolean;",
    )
    .await;
    transform_dts_test(
      r#"export const foo = false;"#,
      "export declare const foo: boolean;",
    )
    .await;
    transform_dts_test(
      r#"export const foo = null;"#,
      "export declare const foo: null;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = undefined;"#,
      "export declare let foo: any;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = 10n;"#,
      "export declare let foo: bigint;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = /foo/;"#,
      "export declare let foo: RegExp;",
    )
    .await;
  }

  #[tokio::test]
  async fn dts_fn_expr() {
    transform_dts_test(
      r#"export let foo = function add(a: number, b: number): number {
  return a + b;
}"#,
      "export declare let foo: (a: number, b: number) => number;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = function add<T>([a, b]: T): void {}"#,
      "export declare let foo: <T>([a, b]: T) => void;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = function add<T>({a, b}: T): void {}"#,
      "export declare let foo: <T>({ a, b }: T) => void;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = function add(a = 2): void {}"#,
      "export declare let foo: (a: number) => void;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = function add(...params: any[]): void {}"#,
      "export declare let foo: (...params: any[]) => void;",
    )
    .await;
  }

  #[tokio::test]
  async fn dts_fn_arrow_expr() {
    transform_dts_test(
      r#"export let foo = (a: number, b: number): number => {
  return a + b;
}"#,
      "export declare let foo: (a: number, b: number) => number;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = <T>([a, b]: T): void => {}"#,
      "export declare let foo: <T>([a, b]: T) => void;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = <T>({a, b}: T): void => {}"#,
      "export declare let foo: <T>({ a, b }: T) => void;",
    )
    .await;
    transform_dts_test(
      r#"export let foo = (a = 2): void => {}"#,
      "export declare let foo: (a: number) => void;",
    )
    .await;

    transform_dts_test(
      r#"export let foo = (...params: any[]): void => {}"#,
      "export declare let foo: (...params: any[]) => void;",
    )
    .await;
  }

  #[tokio::test]
  async fn dts_type_export() {
    transform_dts_test(r#"interface Foo {}"#, "interface Foo {}").await;
    transform_dts_test(r#"type Foo = number;"#, "type Foo = number;").await;

    transform_dts_test(r#"export interface Foo {}"#, "export interface Foo {}")
      .await;
    transform_dts_test(
      r#"export type Foo = number;"#,
      "export type Foo = number;",
    )
    .await;
  }

  #[tokio::test]
  async fn dts_enum_export() {
    transform_dts_test(
      r#"export enum Foo { A, B }"#,
      "export declare enum Foo {\n  A,\n  B\n}",
    )
    .await;
    transform_dts_test(
      r#"export const enum Foo { A, B }"#,
      "export declare const enum Foo {\n  A,\n  B\n}",
    )
    .await;

    transform_dts_test(
      r#"export enum Foo { A = "foo", B = "bar" }"#,
      r#"export declare enum Foo {
  A = "foo",
  B = "bar"
}"#,
    )
    .await;

    // TODO: Enum rules https://www.typescriptlang.org/docs/handbook/enums.html
  }

  #[tokio::test]
  async fn dts_default_export() {
    transform_dts_test(
      r#"export default function(a: number, b: number): number {};"#,
      "export default function(a: number, b: number): number;",
    )
    .await;
    transform_dts_test(
      r#"export default function(a: number, b: number): number;
export default function(a: number, b: number): any {
  return foo
};"#,
      "export default function(a: number, b: number): number;",
    )
    .await;
    transform_dts_test(
      r#"export default class {foo = 2};"#,
      r#"export default class {
  foo: number;
}"#,
    )
    .await;
    transform_dts_test(
      r#"export default 42;"#,
      r#"declare const _dts_1: number;
export default _dts_1;"#,
    )
    .await;
    // TODO
    //     transform_dts_test(
    //       r#"const a: number = 42; export default a;"#,
    //       r#"declare const a: number;
    // export default a;"#,
    //     )
    //     .await;
  }

  #[tokio::test]
  async fn dts_default_export_named() {
    transform_dts_test(
      r#"export { foo, bar } from "foo";"#,
      r#"export { foo, bar } from "foo";"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_default_export_all() {
    transform_dts_test(
      r#"export * as foo from "foo";"#,
      r#"export * as foo from "foo";"#,
    )
    .await;
  }

  #[tokio::test]
  async fn dts_imports() {
    transform_dts_test(
      r#"import { foo } from "bar";export const foobar = foo;"#,
      r#"import { foo } from "bar";
export declare const foobar: any;"#,
    )
    .await;
  }
}
