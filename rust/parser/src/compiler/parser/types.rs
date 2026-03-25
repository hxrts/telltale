//! Internal AST types for parsing.
//!
//! These types represent the intermediate parse tree before conversion
//! to the final Protocol AST.

use crate::ast::{AuthorityBindingMode, CommitmentOutcome, ProgressAttachment, Role};
use proc_macro2::{Ident, TokenStream};
use quote::quote;
use std::collections::HashMap;
use syn::{BinOp, Expr, Lit, UnOp};

/// Choreography statement types
#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)] // Statement enum is internal to parser; performance impact is minimal
pub(crate) enum Statement {
    Begin {
        operation: String,
        args: Vec<String>,
        progress: Option<ProgressAttachment>,
    },
    Await {
        operation: String,
    },
    Resolve {
        operation: String,
        outcome: CommitmentOutcome,
    },
    Invalidate {
        operation: String,
    },
    Let {
        name: String,
        mode: AuthorityBindingMode,
        expr: AuthorityExprSpec,
        body: Option<Vec<Statement>>,
    },
    Case {
        expr: AuthorityExprSpec,
        branches: Vec<CaseBranchSpec>,
    },
    Timeout {
        role: Role,
        duration_ms: u64,
        body: Vec<Statement>,
        on_timeout: Vec<Statement>,
        on_cancel: Option<Vec<Statement>>,
    },
    Send {
        from: Role,
        to: Role,
        message: MessageSpec,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
        to_annotations: HashMap<String, String>,
    },
    Broadcast {
        from: Role,
        message: MessageSpec,
        annotations: HashMap<String, String>,
        from_annotations: HashMap<String, String>,
    },
    Choice {
        role: Role,
        branches: Vec<ChoiceBranch>,
        annotations: HashMap<String, String>,
    },
    Loop {
        condition: Option<crate::ast::Condition>,
        body: Vec<Statement>,
    },
    Parallel {
        branches: Vec<Vec<Statement>>,
    },
    Rec {
        label: Ident,
        body: Vec<Statement>,
    },
    /// Recursive back-reference (continue to a rec label)
    Continue {
        label: Ident,
    },
    Call {
        name: Ident,
    },
    Publish {
        event: String,
        arg: Option<String>,
    },
    PublishAuthority {
        witness: String,
        publication_name: String,
    },
    Materialize {
        proof: String,
        publication: String,
    },
    Handoff {
        operation: String,
        target: Role,
        receipt: String,
    },
    DependentWork {
        name: String,
        arg: Option<String>,
        required_for: String,
    },
}

/// Choice branch in choreography
#[derive(Debug, Clone)]
pub(crate) struct ChoiceBranch {
    pub label: Ident,
    pub guard: Option<ChoiceGuardSpec>,
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub(crate) struct CaseBranchSpec {
    pub pattern: CasePatternSpec,
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone)]
pub(crate) struct CasePatternSpec {
    pub constructor: String,
    pub binders: Vec<String>,
}

#[derive(Debug, Clone)]
pub(crate) enum AuthorityExprSpec {
    Var(String),
    Check {
        effect: String,
        operation: String,
        args: Vec<String>,
    },
    Observe {
        effect: String,
        operation: String,
        args: Vec<String>,
    },
    Transfer {
        subject: String,
        from: String,
        to: String,
    },
    Constructor {
        name: String,
        arg: Option<String>,
    },
    Call {
        name: String,
        args: Vec<String>,
    },
}

#[derive(Debug, Clone)]
pub(crate) enum ChoiceGuardSpec {
    Predicate(TokenStream),
    Evidence {
        effect: String,
        operation: String,
        args: Vec<String>,
        binding: String,
    },
}

/// Message specification with optional payload
#[derive(Debug, Clone)]
pub(crate) struct MessageSpec {
    pub name: Ident,
    pub type_annotation: Option<TokenStream>,
    pub payload: Option<TokenStream>,
}

/// Parsed protocol body result
pub(crate) struct ParsedBody {
    pub roles: Option<Vec<Role>>,
    pub statements: Vec<Statement>,
}

/// Typed predicate IR for guard and loop condition parsing.
#[derive(Debug, Clone)]
pub(crate) enum PredicateExpr {
    BoolLiteral(bool),
    Atom(String),
    Not(Box<PredicateExpr>),
    And(Box<PredicateExpr>, Box<PredicateExpr>),
    Or(Box<PredicateExpr>, Box<PredicateExpr>),
    Eq(Box<PredicateExpr>, Box<PredicateExpr>),
    Ne(Box<PredicateExpr>, Box<PredicateExpr>),
    Lt(Box<PredicateExpr>, Box<PredicateExpr>),
    Le(Box<PredicateExpr>, Box<PredicateExpr>),
    Gt(Box<PredicateExpr>, Box<PredicateExpr>),
    Ge(Box<PredicateExpr>, Box<PredicateExpr>),
}

impl PredicateExpr {
    pub(crate) fn parse(src: &str) -> Result<Self, String> {
        let expr = syn::parse_str::<Expr>(src).map_err(|e| e.to_string())?;
        Self::from_syn_expr(expr)
    }

    pub(crate) fn to_token_stream(&self) -> TokenStream {
        match self {
            Self::BoolLiteral(v) => quote!(#v),
            Self::Atom(src) => syn::parse_str::<TokenStream>(src).unwrap_or_else(|_| quote!(false)),
            Self::Not(inner) => {
                let inner_ts = inner.to_token_stream();
                quote!(!(#inner_ts))
            }
            Self::And(lhs, rhs) => {
                let lhs_ts = lhs.to_token_stream();
                let rhs_ts = rhs.to_token_stream();
                quote!((#lhs_ts) && (#rhs_ts))
            }
            Self::Or(lhs, rhs) => {
                let lhs_ts = lhs.to_token_stream();
                let rhs_ts = rhs.to_token_stream();
                quote!((#lhs_ts) || (#rhs_ts))
            }
            Self::Eq(lhs, rhs) => {
                let lhs_ts = lhs.to_token_stream();
                let rhs_ts = rhs.to_token_stream();
                quote!((#lhs_ts) == (#rhs_ts))
            }
            Self::Ne(lhs, rhs) => {
                let lhs_ts = lhs.to_token_stream();
                let rhs_ts = rhs.to_token_stream();
                quote!((#lhs_ts) != (#rhs_ts))
            }
            Self::Lt(lhs, rhs) => {
                let lhs_ts = lhs.to_token_stream();
                let rhs_ts = rhs.to_token_stream();
                quote!((#lhs_ts) < (#rhs_ts))
            }
            Self::Le(lhs, rhs) => {
                let lhs_ts = lhs.to_token_stream();
                let rhs_ts = rhs.to_token_stream();
                quote!((#lhs_ts) <= (#rhs_ts))
            }
            Self::Gt(lhs, rhs) => {
                let lhs_ts = lhs.to_token_stream();
                let rhs_ts = rhs.to_token_stream();
                quote!((#lhs_ts) > (#rhs_ts))
            }
            Self::Ge(lhs, rhs) => {
                let lhs_ts = lhs.to_token_stream();
                let rhs_ts = rhs.to_token_stream();
                quote!((#lhs_ts) >= (#rhs_ts))
            }
        }
    }

    fn from_syn_expr(expr: Expr) -> Result<Self, String> {
        match expr {
            Expr::Binary(binary) => {
                let lhs = Box::new(Self::from_syn_expr(*binary.left)?);
                let rhs = Box::new(Self::from_syn_expr(*binary.right)?);
                match binary.op {
                    BinOp::And(_) => Ok(Self::And(lhs, rhs)),
                    BinOp::Or(_) => Ok(Self::Or(lhs, rhs)),
                    BinOp::Eq(_) => Ok(Self::Eq(lhs, rhs)),
                    BinOp::Ne(_) => Ok(Self::Ne(lhs, rhs)),
                    BinOp::Lt(_) => Ok(Self::Lt(lhs, rhs)),
                    BinOp::Le(_) => Ok(Self::Le(lhs, rhs)),
                    BinOp::Gt(_) => Ok(Self::Gt(lhs, rhs)),
                    BinOp::Ge(_) => Ok(Self::Ge(lhs, rhs)),
                    _ => Err("predicate must be boolean-like".to_string()),
                }
            }
            Expr::Unary(unary) => match unary.op {
                UnOp::Not(_) => Ok(Self::Not(Box::new(Self::from_syn_expr(*unary.expr)?))),
                _ => Err("predicate must be boolean-like".to_string()),
            },
            Expr::Paren(paren) => Self::from_syn_expr(*paren.expr),
            Expr::Group(group) => Self::from_syn_expr(*group.expr),
            Expr::Lit(lit) => match lit.lit {
                Lit::Bool(v) => Ok(Self::BoolLiteral(v.value)),
                _ => Ok(Self::Atom(quote!(#lit).to_string())),
            },
            Expr::Path(expr) => Ok(Self::Atom(quote!(#expr).to_string())),
            Expr::Field(expr) => Ok(Self::Atom(quote!(#expr).to_string())),
            Expr::Index(expr) => Ok(Self::Atom(quote!(#expr).to_string())),
            Expr::Call(expr) => Ok(Self::Atom(quote!(#expr).to_string())),
            Expr::MethodCall(expr) => Ok(Self::Atom(quote!(#expr).to_string())),
            Expr::Macro(expr) => Ok(Self::Atom(quote!(#expr).to_string())),
            _ => Err("predicate must be boolean-like".to_string()),
        }
    }
}
