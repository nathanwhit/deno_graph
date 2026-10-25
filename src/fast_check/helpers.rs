// Copyright 2018-2024 the Deno authors. MIT license.

use std::ops::ControlFlow;

use deno_ast::oxc::allocator::Allocator;
use deno_ast::oxc::allocator::Box;
use deno_ast::oxc::allocator::CloneIn;
use deno_ast::oxc::ast::ast::*;
use deno_ast::oxc::ast::builder::AstBuilder;
use deno_ast::oxc::semantic::Scoping;
use deno_ast::oxc::span::Ident;
use deno_ast::oxc::span::SPAN;

use crate::symbols::helpers::ToId;
use crate::symbols::helpers::is_unresolved_id;

pub fn new_ident<'a>(
  allocator: &'a Allocator,
  name: &str,
) -> BindingIdentifier<'a> {
  BindingIdentifier::new(
    SPAN,
    Ident::from(allocator.alloc_str(name)),
    &AstBuilder::new(allocator),
  )
}

pub fn ts_keyword_type<'a>(
  allocator: &'a Allocator,
  kind: TSKeywordKind,
) -> TSType<'a> {
  match kind {
    TSKeywordKind::Any => TSType::TSAnyKeyword(Box::new_in(
      TSAnyKeyword::new(SPAN, &AstBuilder::new(allocator)),
      &allocator,
    )),
    TSKeywordKind::Unknown => TSType::TSUnknownKeyword(Box::new_in(
      TSUnknownKeyword::new(SPAN, &AstBuilder::new(allocator)),
      &allocator,
    )),
    TSKeywordKind::Boolean => TSType::TSBooleanKeyword(Box::new_in(
      TSBooleanKeyword::new(SPAN, &AstBuilder::new(allocator)),
      &allocator,
    )),
    TSKeywordKind::Number => TSType::TSNumberKeyword(Box::new_in(
      TSNumberKeyword::new(SPAN, &AstBuilder::new(allocator)),
      &allocator,
    )),
    TSKeywordKind::String => TSType::TSStringKeyword(Box::new_in(
      TSStringKeyword::new(SPAN, &AstBuilder::new(allocator)),
      &allocator,
    )),
    TSKeywordKind::Void => TSType::TSVoidKeyword(Box::new_in(
      TSVoidKeyword::new(SPAN, &AstBuilder::new(allocator)),
      &allocator,
    )),
    TSKeywordKind::Null => TSType::TSNullKeyword(Box::new_in(
      TSNullKeyword::new(SPAN, &AstBuilder::new(allocator)),
      &allocator,
    )),
    TSKeywordKind::BigInt => TSType::TSBigIntKeyword(Box::new_in(
      TSBigIntKeyword::new(SPAN, &AstBuilder::new(allocator)),
      &allocator,
    )),
  }
}

/// Enum to represent the keyword types we use in the helpers,
/// since OXC doesn't have a unified TsKeywordTypeKind.
pub enum TSKeywordKind {
  Any,
  Unknown,
  Boolean,
  Number,
  String,
  Void,
  Null,
  BigInt,
}

#[derive(Debug)]
pub enum ReturnStatementAnalysis {
  /// There are no return statements in the function body.
  None,
  /// There are only return statements without arguments in the function body,
  /// or if the function body is empty.
  Void,
  /// There is only a single return statement in the function body, and it has
  /// an argument.
  Single,
  /// There are multiple return statements in the function body, and at least
  /// one of them has an argument.
  Multiple,
}

pub fn analyze_return_stmts_in_function_body(
  body: &FunctionBody<'_>,
) -> ReturnStatementAnalysis {
  if body.statements.is_empty() {
    ReturnStatementAnalysis::Void
  } else {
    let mut analysis = ReturnStatementAnalysis::None;
    _ = analyze_return_stmts_from_stmts(&body.statements, &mut analysis);
    analysis
  }
}

fn analyze_return_stmts_from_stmts(
  stmts: &[Statement<'_>],
  analysis: &mut ReturnStatementAnalysis,
) -> ControlFlow<(), ()> {
  for stmt in stmts {
    analyze_return_stmts_from_stmt(stmt, analysis)?;
  }
  ControlFlow::Continue(())
}

fn analyze_return_stmts_from_stmt(
  stmt: &Statement<'_>,
  analysis: &mut ReturnStatementAnalysis,
) -> ControlFlow<(), ()> {
  match stmt {
    Statement::BlockStatement(n) => {
      analyze_return_stmts_from_stmts(&n.body, analysis)
    }
    Statement::WithStatement(n) => {
      analyze_return_stmts_from_stmt(&n.body, analysis)
    }
    Statement::ReturnStatement(n) => {
      match (&n.argument, &*analysis) {
        (None, ReturnStatementAnalysis::None) => {
          *analysis = ReturnStatementAnalysis::Void;
        }
        (None, ReturnStatementAnalysis::Void) => {}
        (Some(_), ReturnStatementAnalysis::None)
        | (Some(_), ReturnStatementAnalysis::Void) => {
          *analysis = ReturnStatementAnalysis::Single;
        }
        (_, ReturnStatementAnalysis::Single) => {
          *analysis = ReturnStatementAnalysis::Multiple;
          return ControlFlow::Break(());
        }
        (_, ReturnStatementAnalysis::Multiple) => unreachable!(),
      }
      ControlFlow::Continue(())
    }
    Statement::LabeledStatement(n) => {
      analyze_return_stmts_from_stmt(&n.body, analysis)
    }
    Statement::IfStatement(n) => {
      analyze_return_stmts_from_stmt(&n.consequent, analysis)
    }
    Statement::SwitchStatement(n) => {
      for case in &n.cases {
        analyze_return_stmts_from_stmts(&case.consequent, analysis)?;
      }
      ControlFlow::Continue(())
    }
    Statement::TryStatement(n) => {
      analyze_return_stmts_from_stmts(&n.block.body, analysis)?;
      if let Some(n) = &n.handler {
        analyze_return_stmts_from_stmts(&n.body.body, analysis)?;
      }
      if let Some(n) = &n.finalizer {
        analyze_return_stmts_from_stmts(&n.body, analysis)?;
      }
      ControlFlow::Continue(())
    }
    Statement::WhileStatement(n) => {
      analyze_return_stmts_from_stmt(&n.body, analysis)
    }
    Statement::DoWhileStatement(n) => {
      analyze_return_stmts_from_stmt(&n.body, analysis)
    }
    Statement::ForStatement(n) => {
      analyze_return_stmts_from_stmt(&n.body, analysis)
    }
    Statement::ForInStatement(n) => {
      analyze_return_stmts_from_stmt(&n.body, analysis)
    }
    Statement::ForOfStatement(n) => {
      analyze_return_stmts_from_stmt(&n.body, analysis)
    }
    Statement::BreakStatement(_)
    | Statement::ContinueStatement(_)
    | Statement::ThrowStatement(_)
    | Statement::DebuggerStatement(_)
    | Statement::EmptyStatement(_)
    | Statement::ExpressionStatement(_) => ControlFlow::Continue(()),
    // Declaration and module declaration variants
    _ => ControlFlow::Continue(()),
  }
}

pub fn is_void_type(return_type: &TSType) -> bool {
  matches!(return_type, TSType::TSVoidKeyword(_))
}

pub fn any_type_ann<'a>(
  allocator: &'a Allocator,
) -> Box<'a, TSTypeAnnotation<'a>> {
  type_ann(allocator, ts_keyword_type(allocator, TSKeywordKind::Any))
}

pub fn ts_readonly<'a>(
  allocator: &'a Allocator,
  ann: TSType<'a>,
) -> TSType<'a> {
  TSType::TSTypeOperatorType(Box::new_in(
    TSTypeOperator::new(
      SPAN,
      TSTypeOperatorOperator::Readonly,
      ann,
      &AstBuilder::new(allocator),
    ),
    &allocator,
  ))
}

pub fn type_ann<'a>(
  allocator: &'a Allocator,
  ts_type: TSType<'a>,
) -> Box<'a, TSTypeAnnotation<'a>> {
  Box::new_in(
    TSTypeAnnotation::new(SPAN, ts_type, &AstBuilder::new(allocator)),
    &allocator,
  )
}

pub fn type_ref<'a>(
  allocator: &'a Allocator,
  name: &str,
) -> TSTypeReference<'a> {
  TSTypeReference::new(
    SPAN,
    TSTypeName::IdentifierReference(Box::new_in(
      IdentifierReference::new(
        SPAN,
        Ident::from(allocator.alloc_str(name)),
        &AstBuilder::new(allocator),
      ),
      &allocator,
    )),
    None,
    &AstBuilder::new(allocator),
  )
}

pub fn ts_lit_type<'a>(
  allocator: &'a Allocator,
  lit: TSLiteral<'a>,
) -> TSType<'a> {
  TSType::TSLiteralType(Box::new_in(
    TSLiteralType::new(SPAN, lit, &AstBuilder::new(allocator)),
    &allocator,
  ))
}

pub fn regex_type<'a>(allocator: &'a Allocator) -> TSType<'a> {
  TSType::TSTypeReference(Box::new_in(
    type_ref(allocator, "RegExp"),
    &allocator,
  ))
}

/// Convert a TSType into a TSTupleElement.
pub fn ts_tuple_element<'a>(ts_type: TSType<'a>) -> TSTupleElement<'a> {
  TSTupleElement::from(ts_type)
}

pub enum DeclMutabilityKind {
  Const,
  Mutable,
}

pub fn maybe_lit_to_ts_type<'a>(
  allocator: &'a Allocator,
  expr: &Expression<'a>,
  decl_kind: DeclMutabilityKind,
) -> Option<TSType<'a>> {
  match decl_kind {
    DeclMutabilityKind::Const => match expr {
      Expression::StringLiteral(lit_str) => Some(ts_lit_type(
        allocator,
        TSLiteral::StringLiteral(Box::new_in(
          lit_str.as_ref().clone_in(allocator),
          &allocator,
        )),
      )),
      Expression::BooleanLiteral(lit_bool) => Some(ts_lit_type(
        allocator,
        TSLiteral::BooleanLiteral(Box::new_in(
          lit_bool.as_ref().clone_in(allocator),
          &allocator,
        )),
      )),
      Expression::NullLiteral(_) => {
        Some(ts_keyword_type(allocator, TSKeywordKind::Null))
      }
      Expression::NumericLiteral(lit_num) => Some(ts_lit_type(
        allocator,
        TSLiteral::NumericLiteral(Box::new_in(
          lit_num.as_ref().clone_in(allocator),
          &allocator,
        )),
      )),
      Expression::BigIntLiteral(lit_bigint) => Some(ts_lit_type(
        allocator,
        TSLiteral::BigIntLiteral(Box::new_in(
          lit_bigint.as_ref().clone_in(allocator),
          &allocator,
        )),
      )),
      Expression::RegExpLiteral(_) => Some(regex_type(allocator)),
      _ => None,
    },
    DeclMutabilityKind::Mutable => match expr {
      Expression::StringLiteral(_) => {
        Some(ts_keyword_type(allocator, TSKeywordKind::String))
      }
      Expression::BooleanLiteral(_) => {
        Some(ts_keyword_type(allocator, TSKeywordKind::Boolean))
      }
      Expression::NullLiteral(_) => {
        Some(ts_keyword_type(allocator, TSKeywordKind::Null))
      }
      Expression::NumericLiteral(_) => {
        Some(ts_keyword_type(allocator, TSKeywordKind::Number))
      }
      Expression::BigIntLiteral(_) => {
        Some(ts_keyword_type(allocator, TSKeywordKind::BigInt))
      }
      Expression::RegExpLiteral(_) => Some(regex_type(allocator)),
      _ => None,
    },
  }
}

/// Whether the identifier reference is unresolved (i.e. refers to a global).
pub fn is_global_ident(
  ident: &IdentifierReference,
  scoping: Option<&Scoping>,
) -> bool {
  is_unresolved_id(&ident.to_id(scoping))
}

/// Gets the argument of an `Object.freeze(...)` call where `Object` is
/// the global object, if the call expression matches that shape.
pub fn object_freeze_call_arg<'a, 'b>(
  call_expr: &'b CallExpression<'a>,
  scoping: Option<&Scoping>,
) -> Option<&'b Expression<'a>> {
  let Expression::StaticMemberExpression(member_expr) = &call_expr.callee
  else {
    return None;
  };
  let Expression::Identifier(obj_ident) = &member_expr.object else {
    return None;
  };
  if obj_ident.name != "Object" || !is_global_ident(obj_ident, scoping) {
    return None;
  }
  if member_expr.property.name != "freeze" {
    return None;
  }
  if call_expr.arguments.len() != 1 {
    return None;
  }
  // a spread argument is not an expression
  call_expr.arguments.first()?.as_expression()
}

/// Gets the type of an untagged template literal expression.
///
/// A template literal without substitutions is equivalent to a string
/// literal, so it keeps its literal type in a const position. Otherwise
/// the type depends on the substituted expressions, which TypeScript only
/// evaluates in a const assertion (that case is handled by leaving the
/// expression as-is instead of inferring a type from it).
pub fn tpl_to_ts_type<'a>(
  allocator: &'a Allocator,
  tpl: &TemplateLiteral<'a>,
  decl_kind: DeclMutabilityKind,
) -> TSType<'a> {
  if let DeclMutabilityKind::Const = decl_kind
    && tpl.expressions.is_empty()
    && let Some(quasi) = tpl.quasis.first()
    && let Some(cooked) = quasi.value.cooked
  {
    return ts_lit_type(
      allocator,
      TSLiteral::StringLiteral(Box::new_in(
        StringLiteral::new(SPAN, cooked, None, &AstBuilder::new(allocator)),
        &allocator,
      )),
    );
  }

  ts_keyword_type(allocator, TSKeywordKind::String)
}
