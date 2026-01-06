//! Parser for choreographic protocol syntax.
//!
//! This module provides a full implementation using Pest grammar for parsing
//! choreographic DSL specifications into the Protocol AST.
//!
//! # Module Structure
//!
//! - [`error`]: Error types and span information for diagnostics
//! - [`types`]: Internal AST types for parsing (Statement, ChoiceBranch, etc.)
//! - [`role`]: Role parsing (declarations, references, indices, ranges)
//! - [`statement`]: Statement parsing (send, choice, loop, etc.)
//! - [`conversion`]: Protocol conversion and call inlining

mod conversion;
mod error;
mod role;
mod statement;
mod stmt_parsers;
mod types;

// Re-export public API
pub use error::{ErrorSpan, ParseError};

use crate::ast::Choreography;
use crate::compiler::layout::preprocess_layout;
use crate::extensions::{ExtensionRegistry, ProtocolExtension};
use pest::Parser;
use pest_derive::Parser;
use proc_macro2::{Span, TokenStream};
use quote::format_ident;
use std::collections::{HashMap, HashSet};

use conversion::{convert_statements_to_protocol, inline_calls};
use role::parse_roles_from_pair;
use statement::{parse_local_protocol_decl, parse_protocol_body};
use types::Statement;

#[derive(Parser)]
#[grammar = "compiler/choreography.pest"]
struct ChoreographyParser;

/// Parse a namespace declaration from the AST
fn parse_module_decl(
    pair: pest::iterators::Pair<Rule>,
    input: &str,
) -> std::result::Result<String, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();
    if let Some(ident) = inner.next() {
        if ident.as_rule() == Rule::ident {
            return Ok(ident.as_str().to_string());
        }
    }
    Err(ParseError::Syntax {
        span: ErrorSpan::from_pest_span(span, input),
        message: "Invalid module declaration".to_string(),
    })
}

/// Parse a choreographic protocol from a string
pub fn parse_choreography_str(input: &str) -> std::result::Result<Choreography, ParseError> {
    parse_choreography_str_with_extensions(input, &ExtensionRegistry::new())
        .map(|(choreo, _)| choreo)
}

/// Parse a choreographic protocol from a string with extension support
pub fn parse_choreography_str_with_extensions(
    input: &str,
    registry: &ExtensionRegistry,
) -> std::result::Result<(Choreography, Vec<Box<dyn ProtocolExtension>>), ParseError> {
    let dedented = strip_common_indent(input);
    let layout = preprocess_layout(&dedented).map_err(|e| ParseError::Layout {
        span: ErrorSpan::from_line_col(e.line, e.column, &dedented),
        message: e.message,
    })?;

    let preprocessed = preprocess_extension_syntax(&layout, registry)?;

    let pairs = ChoreographyParser::parse(Rule::choreography, &preprocessed).map_err(Box::new)?;

    let mut name = format_ident!("Unnamed");
    let mut namespace: Option<String> = None;
    let mut roles: Vec<crate::ast::Role> = Vec::new();
    let mut declared_roles: HashSet<String> = HashSet::new();
    let mut protocol_defs: HashMap<String, Vec<Statement>> = HashMap::new();
    let mut statements: Vec<Statement> = Vec::new();

    for pair in pairs {
        if pair.as_rule() == Rule::choreography {
            for inner in pair.into_inner() {
                match inner.as_rule() {
                    Rule::module_decl => {
                        namespace = Some(parse_module_decl(inner, &preprocessed)?);
                    }
                    Rule::import_decl => {
                        // Imports are parsed for completeness but ignored for now.
                    }
                    Rule::protocol_decl => {
                        let mut proto_inner = inner.into_inner();
                        let name_pair = proto_inner
                            .next()
                            .expect("grammar: protocol_decl must have name");
                        name = format_ident!("{}", name_pair.as_str());

                        let mut header_roles: Option<Vec<crate::ast::Role>> = None;
                        let mut body_pair: Option<pest::iterators::Pair<Rule>> = None;
                        let mut where_pair: Option<pest::iterators::Pair<Rule>> = None;

                        for item in proto_inner {
                            match item.as_rule() {
                                Rule::header_roles => {
                                    header_roles =
                                        Some(parse_roles_from_pair(item, &preprocessed)?);
                                }
                                Rule::protocol_body => {
                                    body_pair = Some(item);
                                }
                                Rule::where_block => {
                                    where_pair = Some(item);
                                }
                                _ => {}
                            }
                        }

                        let allow_roles_decl = header_roles.is_none();
                        let body_pair = body_pair.expect("grammar: protocol_decl must have body");
                        let body_span = body_pair.as_span();
                        let types::ParsedBody {
                            roles: body_roles,
                            statements: body_statements,
                        } = parse_protocol_body(
                            body_pair,
                            &declared_roles,
                            &preprocessed,
                            &protocol_defs,
                            allow_roles_decl,
                        )?;

                        if header_roles.is_some() && body_roles.is_some() {
                            return Err(ParseError::Syntax {
                                span: ErrorSpan::from_pest_span(body_span, &preprocessed),
                                message: "roles cannot be declared both in the header and body"
                                    .to_string(),
                            });
                        }

                        if let Some(r) = header_roles {
                            roles = r;
                            declared_roles = roles.iter().map(|r| r.name().to_string()).collect();
                        } else if let Some(r) = body_roles {
                            roles = r;
                            declared_roles = roles.iter().map(|r| r.name().to_string()).collect();
                        }

                        if let Some(where_block) = where_pair {
                            for local in where_block.into_inner().flat_map(|p| p.into_inner()) {
                                if local.as_rule() == Rule::local_protocol_decl {
                                    parse_local_protocol_decl(
                                        local,
                                        &declared_roles,
                                        &preprocessed,
                                        &mut protocol_defs,
                                    )?;
                                }
                            }
                        }

                        statements = inline_calls(&body_statements, &protocol_defs, &preprocessed)?;
                    }
                    _ => {}
                }
            }
        }
    }

    if roles.is_empty() {
        return Err(ParseError::EmptyChoreography);
    }

    let protocol = convert_statements_to_protocol(&statements, &roles);

    Ok((
        Choreography {
            name,
            namespace,
            roles,
            protocol,
            attrs: HashMap::new(),
        },
        Vec::new(),
    ))
}

/// Preprocess extension syntax to transform it into standard DSL syntax.
///
/// The new DSL drops annotation/extension surface syntax for now, so this is a
/// no-op placeholder that keeps the API stable.
fn preprocess_extension_syntax(
    input: &str,
    _registry: &ExtensionRegistry,
) -> std::result::Result<String, ParseError> {
    Ok(input.to_string())
}

fn strip_common_indent(input: &str) -> String {
    let lines: Vec<&str> = input.lines().collect();
    let mut min_indent: Option<usize> = None;

    for line in &lines {
        if line.trim().is_empty() {
            continue;
        }
        let indent = line.chars().take_while(|c| *c == ' ').count();
        min_indent = Some(match min_indent {
            Some(current) => current.min(indent),
            None => indent,
        });
    }

    let min_indent = min_indent.unwrap_or(0);
    if min_indent == 0 {
        return input.to_string();
    }

    let mut out = String::new();
    for (idx, line) in lines.iter().enumerate() {
        let stripped = line.get(min_indent..).unwrap_or(line);
        out.push_str(stripped);
        if idx + 1 < lines.len() {
            out.push('\n');
        }
    }

    if input.ends_with('\n') {
        out.push('\n');
    }

    out
}

/// Parse a choreographic protocol from a token stream (for macro use)
/// This is a compatibility function that wraps the string parser
pub fn parse_choreography(input: TokenStream) -> syn::Result<Choreography> {
    use syn::LitStr;

    // Try to parse as a string literal (for DSL syntax)
    if let Ok(lit_str) = syn::parse2::<LitStr>(input.clone()) {
        // Parse the DSL string
        let dsl_content = lit_str.value();
        return parse_choreography_str(&dsl_content).map_err(|e| {
            syn::Error::new(lit_str.span(), format!("Choreography parse error: {e}"))
        });
    }

    // If not a string literal, return an error with helpful message
    Err(syn::Error::new(
        proc_macro2::Span::call_site(),
        "choreography! macro expects a string literal containing the choreography DSL.\n\
         Example usage:\n\
         choreography! { r#\"\n\
         protocol MyProtocol =\n\
           roles Alice, Bob\n\
           Alice -> Bob : Hello\n\
         \"# }",
    ))
}

/// Parse a choreography from a file
pub fn parse_choreography_file(
    path: &std::path::Path,
) -> std::result::Result<Choreography, ParseError> {
    let content = std::fs::read_to_string(path).map_err(|e| ParseError::Syntax {
        span: ErrorSpan {
            line: 1,
            column: 1,
            line_end: 1,
            column_end: 1,
            snippet: format!("Failed to read file: {}", path.display()),
        },
        message: e.to_string(),
    })?;

    parse_choreography_str(&content)
}

/// Parse choreography DSL
pub fn parse_dsl(input: &str) -> std::result::Result<Choreography, ParseError> {
    parse_choreography_str(input)
}

// Example of how the macro would work
#[doc(hidden)]
#[must_use]
pub fn choreography_macro(input: TokenStream) -> TokenStream {
    let choreography = match parse_choreography(input) {
        Ok(c) => c,
        Err(e) => return e.to_compile_error(),
    };

    // Validate the choreography
    if let Err(e) = choreography.validate() {
        return syn::Error::new(Span::call_site(), e.to_string()).to_compile_error();
    }

    // Project to local types
    let mut local_types = Vec::new();
    for role in &choreography.roles {
        match super::projection::project(&choreography, role) {
            Ok(local_type) => local_types.push((role.clone(), local_type)),
            Err(e) => return syn::Error::new(Span::call_site(), e.to_string()).to_compile_error(),
        }
    }

    // Generate code with namespace support
    super::codegen::generate_choreography_code_with_namespacing(&choreography, &local_types)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Condition, Protocol};

    #[test]
    fn test_parse_simple_send() {
        let input = r#"
protocol SimpleSend =
  roles Alice, Bob
  Alice -> Bob : Hello
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "SimpleSend");
        assert_eq!(choreo.roles.len(), 2);
    }

    #[test]
    fn test_parse_with_choice() {
        let input = r#"
protocol Negotiation =
  roles Buyer, Seller
  Buyer -> Seller : Offer
  case choose Seller of
    accept ->
      Seller -> Buyer : Accept
    reject ->
      Seller -> Buyer : Reject
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "Negotiation");
    }

    #[test]
    fn test_parse_choice_alias() {
        let input = r#"
protocol AliasChoice =
  roles A, B
  choice at A
    ok ->
      A -> B : Ack
    fail ->
      A -> B : Nack
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse alias choice: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_parse_undefined_role() {
        let input = r#"
protocol Invalid =
  roles Alice
  Alice -> Bob : Hello
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, ParseError::UndefinedRole { .. }));

        // Verify error message includes span information
        let err_str = err.to_string();
        assert!(err_str.contains("Undefined role"));
        assert!(err_str.contains("Bob"));
    }

    #[test]
    fn test_parse_duplicate_role() {
        let input = r#"
protocol DuplicateRole =
  roles Alice, Bob, Alice
  Alice -> Bob : Hello
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, ParseError::DuplicateRole { .. }));

        // Verify error message includes span information
        let err_str = err.to_string();
        assert!(err_str.contains("Duplicate role"));
        assert!(err_str.contains("Alice"));
    }

    #[test]
    fn test_parse_loop_repeat() {
        let input = r#"
protocol LoopProtocol =
  roles Client, Server
  loop repeat 3
    Client -> Server : Request
    Server -> Client : Response
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
    }

    #[test]
    fn test_parse_loop_decide() {
        let input = r#"
protocol DecideLoop =
  roles Client, Server
  loop decide by Client
    Client -> Server : Ping
    Server -> Client : Pong
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse decide loop: {:?}",
            result.err()
        );
    }

    #[test]
    fn test_role_decides_desugaring() {
        // RoleDecides loops should be desugared to choice+rec pattern (Option B: fused)
        // loop decide by Client { Client -> Server: Ping; ... }
        // becomes:
        //   rec RoleDecidesLoop {
        //       choice at Client {
        //           Ping { Client -> Server: Ping; ...; continue }
        //           Done { Client -> Server: Done }
        //       }
        //   }
        let input = r#"
protocol DecideLoop =
  roles Client, Server
  loop decide by Client
    Client -> Server : Ping
    Server -> Client : Pong
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse decide loop: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { label, body } => {
                assert_eq!(label.to_string(), "RoleDecidesLoop");
                match body.as_ref() {
                    Protocol::Choice { role, branches, .. } => {
                        assert_eq!(role.name().to_string(), "Client");
                        assert_eq!(branches.len(), 2);

                        // First branch should be the continue branch (using first message label)
                        let continue_branch = branches.first();
                        assert_eq!(continue_branch.label.to_string(), "Ping");

                        // Inside the continue branch, we should have the Send
                        match &continue_branch.protocol {
                            Protocol::Send {
                                from,
                                to,
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(from.name().to_string(), "Client");
                                assert_eq!(to.name().to_string(), "Server");
                                assert_eq!(message.name.to_string(), "Ping");

                                // Continuation should be the response followed by Var (continue)
                                match continuation.as_ref() {
                                    Protocol::Send {
                                        from,
                                        to,
                                        message,
                                        continuation,
                                        ..
                                    } => {
                                        assert_eq!(from.name().to_string(), "Server");
                                        assert_eq!(to.name().to_string(), "Client");
                                        assert_eq!(message.name.to_string(), "Pong");

                                        // Should end with Var (continue RoleDecidesLoop)
                                        match continuation.as_ref() {
                                            Protocol::Var(label) => {
                                                assert_eq!(label.to_string(), "RoleDecidesLoop");
                                            }
                                            _ => panic!(
                                                "Expected Var for continue, got {:?}",
                                                continuation
                                            ),
                                        }
                                    }
                                    _ => panic!("Expected Send for Pong, got {:?}", continuation),
                                }
                            }
                            _ => {
                                panic!("Expected Send for Ping, got {:?}", continue_branch.protocol)
                            }
                        }

                        // Second branch should be Done
                        let done_branch = &branches.as_slice()[1];
                        assert_eq!(done_branch.label.to_string(), "Done");
                        match &done_branch.protocol {
                            Protocol::Send {
                                from,
                                to,
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(from.name().to_string(), "Client");
                                assert_eq!(to.name().to_string(), "Server");
                                assert_eq!(message.name.to_string(), "Done");
                                assert!(matches!(continuation.as_ref(), Protocol::End));
                            }
                            _ => panic!("Expected Send for Done, got {:?}", done_branch.protocol),
                        }
                    }
                    _ => panic!("Expected Choice inside Rec, got {:?}", body),
                }
            }
            _ => panic!("Expected Rec at top level, got {:?}", choreo.protocol),
        }
    }

    #[test]
    fn test_role_decides_wrong_first_sender_no_desugar() {
        // When the first statement is a Send but NOT from the deciding role,
        // the loop should NOT be desugared and should remain as Protocol::Loop
        let input = r#"
protocol WrongSender =
  roles Client, Server
  loop decide by Client
    Server -> Client : Response
    Client -> Server : Ack
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        // Should remain as Loop, not desugared to Rec
        match &choreo.protocol {
            Protocol::Loop { condition, .. } => match condition {
                Some(Condition::RoleDecides(role)) => {
                    assert_eq!(role.name().to_string(), "Client");
                }
                _ => panic!("Expected RoleDecides condition"),
            },
            _ => panic!(
                "Expected Loop (not desugared) when first sender doesn't match deciding role"
            ),
        }
    }

    #[test]
    fn test_role_decides_single_message() {
        // Minimal case: loop with just one message
        let input = r#"
protocol SingleMessage =
  roles A, B
  loop decide by A
    A -> B : Msg
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { label, body } => {
                assert_eq!(label.to_string(), "RoleDecidesLoop");
                match body.as_ref() {
                    Protocol::Choice { role, branches, .. } => {
                        assert_eq!(role.name().to_string(), "A");
                        assert_eq!(branches.len(), 2);

                        // Continue branch
                        let continue_branch = branches.first();
                        assert_eq!(continue_branch.label.to_string(), "Msg");
                        match &continue_branch.protocol {
                            Protocol::Send {
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(message.name.to_string(), "Msg");
                                // Should directly continue (no more statements)
                                assert!(matches!(continuation.as_ref(), Protocol::Var(_)));
                            }
                            _ => panic!("Expected Send"),
                        }

                        // Done branch
                        let done_branch = &branches.as_slice()[1];
                        assert_eq!(done_branch.label.to_string(), "Done");
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_three_roles() {
        // Test with three roles where deciding role sends to one, then another responds
        let input = r#"
protocol ThreeRoles =
  roles Client, Server, Logger
  loop decide by Client
    Client -> Server : Request
    Server -> Logger : Log
    Logger -> Client : Ack
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { role, branches, .. } => {
                        assert_eq!(role.name().to_string(), "Client");

                        let continue_branch = branches.first();
                        assert_eq!(continue_branch.label.to_string(), "Request");

                        // Verify the chain: Request -> Log -> Ack -> continue
                        match &continue_branch.protocol {
                            Protocol::Send {
                                from,
                                to,
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(from.name().to_string(), "Client");
                                assert_eq!(to.name().to_string(), "Server");
                                assert_eq!(message.name.to_string(), "Request");

                                match continuation.as_ref() {
                                    Protocol::Send {
                                        from,
                                        to,
                                        message,
                                        continuation,
                                        ..
                                    } => {
                                        assert_eq!(from.name().to_string(), "Server");
                                        assert_eq!(to.name().to_string(), "Logger");
                                        assert_eq!(message.name.to_string(), "Log");

                                        match continuation.as_ref() {
                                            Protocol::Send {
                                                from,
                                                to,
                                                message,
                                                continuation,
                                                ..
                                            } => {
                                                assert_eq!(from.name().to_string(), "Logger");
                                                assert_eq!(to.name().to_string(), "Client");
                                                assert_eq!(message.name.to_string(), "Ack");
                                                assert!(matches!(
                                                    continuation.as_ref(),
                                                    Protocol::Var(_)
                                                ));
                                            }
                                            _ => panic!("Expected Send for Ack"),
                                        }
                                    }
                                    _ => panic!("Expected Send for Log"),
                                }
                            }
                            _ => panic!("Expected Send for Request"),
                        }

                        // Done branch sends to Server (same as first message target)
                        let done_branch = &branches.as_slice()[1];
                        match &done_branch.protocol {
                            Protocol::Send { from, to, .. } => {
                                assert_eq!(from.name().to_string(), "Client");
                                assert_eq!(to.name().to_string(), "Server");
                            }
                            _ => panic!("Expected Send in Done branch"),
                        }
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_with_type_annotation() {
        // Test that type annotations are preserved through desugaring
        let input = r#"
protocol TypedLoop =
  roles Client, Server
  loop decide by Client
    Client -> Server : Request<String>
    Server -> Client : Response<u32>
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { branches, .. } => {
                        let continue_branch = branches.first();
                        match &continue_branch.protocol {
                            Protocol::Send {
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(message.name.to_string(), "Request");
                                // Type annotation should be preserved
                                assert!(message.type_annotation.is_some());
                                let type_str =
                                    message.type_annotation.as_ref().unwrap().to_string();
                                assert!(
                                    type_str.contains("String"),
                                    "Expected String type, got: {}",
                                    type_str
                                );

                                match continuation.as_ref() {
                                    Protocol::Send { message, .. } => {
                                        assert_eq!(message.name.to_string(), "Response");
                                        assert!(message.type_annotation.is_some());
                                        let type_str =
                                            message.type_annotation.as_ref().unwrap().to_string();
                                        assert!(
                                            type_str.contains("u32"),
                                            "Expected u32 type, got: {}",
                                            type_str
                                        );
                                    }
                                    _ => panic!("Expected Send for Response"),
                                }
                            }
                            _ => panic!("Expected Send for Request"),
                        }
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_first_stmt_is_choice_no_desugar() {
        // When the first statement is NOT a Send (e.g., it's a choice),
        // the loop should NOT be desugared
        let input = r#"
protocol FirstIsChoice =
  roles A, B
  loop decide by A
    choice at A
      opt1 ->
        A -> B : Msg1
      opt2 ->
        A -> B : Msg2
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        // Should remain as Loop, not desugared
        match &choreo.protocol {
            Protocol::Loop { condition, body } => {
                match condition {
                    Some(Condition::RoleDecides(role)) => {
                        assert_eq!(role.name().to_string(), "A");
                    }
                    _ => panic!("Expected RoleDecides condition"),
                }
                // Body should be a Choice
                match body.as_ref() {
                    Protocol::Choice { .. } => {}
                    _ => panic!("Expected Choice in body"),
                }
            }
            _ => panic!("Expected Loop (not desugared) when first statement is not a Send"),
        }
    }

    #[test]
    fn test_role_decides_followed_by_statements() {
        // Test that statements after the loop are preserved
        let input = r#"
protocol LoopThenMore =
  roles A, B
  loop decide by A
    A -> B : Request
    B -> A : Response
  A -> B : Goodbye
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        // The loop should be desugared, followed by the Goodbye send
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { branches, .. } => {
                        // Done branch should continue to the Goodbye message
                        let done_branch = &branches.as_slice()[1];
                        match &done_branch.protocol {
                            Protocol::Send {
                                message,
                                continuation,
                                ..
                            } => {
                                assert_eq!(message.name.to_string(), "Done");
                                // After Done, should be the Goodbye send
                                match continuation.as_ref() {
                                    Protocol::Send { message, .. } => {
                                        assert_eq!(message.name.to_string(), "Goodbye");
                                    }
                                    _ => panic!("Expected Goodbye after Done"),
                                }
                            }
                            _ => panic!("Expected Send in Done branch"),
                        }
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_multiple_loops() {
        // Test two consecutive RoleDecides loops
        let input = r#"
protocol TwoLoops =
  roles A, B
  loop decide by A
    A -> B : First
  loop decide by B
    B -> A : Second
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        // First loop should be Rec
        match &choreo.protocol {
            Protocol::Rec { label, body } => {
                assert_eq!(label.to_string(), "RoleDecidesLoop");
                match body.as_ref() {
                    Protocol::Choice { role, branches, .. } => {
                        assert_eq!(role.name().to_string(), "A");

                        // Done branch should lead to second loop
                        let done_branch = &branches.as_slice()[1];
                        match &done_branch.protocol {
                            Protocol::Send { continuation, .. } => {
                                // After first loop's Done, should be second Rec
                                match continuation.as_ref() {
                                    Protocol::Rec { body, .. } => match body.as_ref() {
                                        Protocol::Choice { role, .. } => {
                                            assert_eq!(role.name().to_string(), "B");
                                        }
                                        _ => panic!("Expected Choice in second loop"),
                                    },
                                    _ => panic!("Expected second Rec after first loop"),
                                }
                            }
                            _ => panic!("Expected Send in Done branch"),
                        }
                    }
                    _ => panic!("Expected Choice in first loop"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_empty_body_edge_case() {
        // Edge case: empty loop body (should parse but not desugar - no first statement)
        // Note: This tests the parser's robustness, not valid protocol design
        let input = r#"
protocol EmptyBody =
  roles A, B
  loop decide by A
  A -> B : AfterLoop
"#;

        // This might fail to parse or produce a Loop with empty body
        // Either way, we should handle it gracefully
        let result = parse_choreography_str(input);
        // Just verify it doesn't panic - the exact behavior depends on grammar
        if let Ok(choreo) = result {
            // If parsed, should not be desugared (no first Send)
            match &choreo.protocol {
                Protocol::Loop { .. } => {
                    // Expected: Loop not desugared due to empty/invalid body
                }
                Protocol::Send { .. } => {
                    // Also acceptable: empty loop might be elided
                }
                _ => {
                    // Any other result is acceptable for this edge case
                }
            }
        }
        // Parsing failure is also acceptable for this malformed input
    }

    #[test]
    fn test_role_decides_preserves_branch_label_from_message() {
        // Verify that the branch label matches the first message name exactly
        let input = r#"
protocol CustomMessageName =
  roles Producer, Consumer
  loop decide by Producer
    Producer -> Consumer : DataChunk
    Consumer -> Producer : Ack
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { branches, .. } => {
                        // First branch label should be "DataChunk" (the message name)
                        let continue_branch = branches.first();
                        assert_eq!(continue_branch.label.to_string(), "DataChunk");

                        // Second branch label should be "Done"
                        let done_branch = &branches.as_slice()[1];
                        assert_eq!(done_branch.label.to_string(), "Done");
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_role_decides_done_message_targets_same_receiver() {
        // The Done message should go to the same receiver as the first message
        let input = r#"
protocol TargetConsistency =
  roles Sender, Receiver, Observer
  loop decide by Sender
    Sender -> Receiver : Data
    Receiver -> Observer : Forward
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => {
                match body.as_ref() {
                    Protocol::Choice { branches, .. } => {
                        // Continue branch sends to Receiver
                        let continue_branch = branches.first();
                        match &continue_branch.protocol {
                            Protocol::Send { to, .. } => {
                                assert_eq!(to.name().to_string(), "Receiver");
                            }
                            _ => panic!("Expected Send"),
                        }

                        // Done branch should also send to Receiver (same target)
                        let done_branch = &branches.as_slice()[1];
                        match &done_branch.protocol {
                            Protocol::Send { from, to, .. } => {
                                assert_eq!(from.name().to_string(), "Sender");
                                assert_eq!(to.name().to_string(), "Receiver");
                            }
                            _ => panic!("Expected Send in Done branch"),
                        }
                    }
                    _ => panic!("Expected Choice"),
                }
            }
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_parse_parallel_branches() {
        let input = r#"
protocol Parallel =
  roles A, B, C, D
  branch
    A -> B : Msg1
  branch
    C -> D : Msg2
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse parallel: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match choreo.protocol {
            Protocol::Parallel { protocols } => {
                assert_eq!(protocols.len(), 2);
            }
            _ => panic!("Expected top-level parallel protocol"),
        }
    }

    #[test]
    fn test_single_branch_is_error() {
        let input = r#"
protocol SingleBranch =
  roles A, B
  branch
    A -> B : Msg
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_err());
        let err = result.unwrap_err();
        let err_str = err.to_string();
        assert!(err_str.contains("parallel requires at least two adjacent branch blocks"));
    }

    #[test]
    fn test_parse_timed_choice() {
        let input = r#"
protocol TimedRequest =
  roles Alice, Bob
  Alice -> Bob : Request
  timed_choice at Alice(5s) {
    OnTime -> {
      Bob -> Alice : Response
    }
    TimedOut -> {
      Alice -> Bob : Cancel
    }
  }
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse timed_choice: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "TimedRequest");

        // Verify timed_choice is desugared to Choice with typed annotation
        match &choreo.protocol {
            Protocol::Send { continuation, .. } => {
                match continuation.as_ref() {
                    Protocol::Choice {
                        role,
                        branches,
                        annotations,
                    } => {
                        assert_eq!(role.name().to_string(), "Alice");
                        assert_eq!(branches.len(), 2);
                        // Check that timed_choice annotation is present
                        assert!(annotations.has_timed_choice());
                        assert_eq!(
                            annotations.timed_choice(),
                            Some(std::time::Duration::from_secs(5))
                        );
                    }
                    _ => panic!("Expected Choice after Send"),
                }
            }
            _ => panic!("Expected Send as first protocol"),
        }
    }

    #[test]
    fn test_parse_timed_choice_milliseconds() {
        let input = r#"
protocol QuickTimeout =
  roles Client, Server
  timed_choice at Client(500ms) {
    Fast -> {
      Server -> Client : Data
    }
    Slow -> {
      Client -> Server : Abort
    }
  }
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse timed_choice with ms: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Choice { annotations, .. } => {
                assert!(annotations.has_timed_choice());
                assert_eq!(
                    annotations.timed_choice(),
                    Some(std::time::Duration::from_millis(500))
                );
            }
            _ => panic!("Expected Choice as first protocol"),
        }
    }

    #[test]
    fn test_parse_timed_choice_minutes() {
        let input = r#"
protocol LongTimeout =
  roles A, B
  timed_choice at A(2m) {
    Done -> {
      B -> A : Complete
    }
    Expired -> {
      A -> B : Timeout
    }
  }
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Choice { annotations, .. } => {
                // 2 minutes = 120000 ms
                assert!(annotations.has_timed_choice());
                assert_eq!(
                    annotations.timed_choice(),
                    Some(std::time::Duration::from_millis(120000))
                );
            }
            _ => panic!("Expected Choice"),
        }
    }

    #[test]
    fn test_parse_heartbeat() {
        let input = r#"
protocol Liveness =
  roles Alice, Bob
  heartbeat Alice -> Bob every 1s on_missing(3) {
    Bob -> Alice : Disconnect
  } body {
    Alice -> Bob : Data
  }
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse heartbeat: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "Liveness");

        // Heartbeat desugars to: rec HeartbeatLoop { ... }
        match &choreo.protocol {
            Protocol::Rec { label, body } => {
                assert_eq!(label.to_string(), "HeartbeatLoop");

                // Inside: Sender -> Receiver: Heartbeat; choice at Receiver { ... }
                match body.as_ref() {
                    Protocol::Send {
                        from,
                        to,
                        message,
                        continuation,
                        ..
                    } => {
                        assert_eq!(from.name().to_string(), "Alice");
                        assert_eq!(to.name().to_string(), "Bob");
                        assert_eq!(message.name.to_string(), "Heartbeat");

                        // Continuation is Choice at Receiver
                        match continuation.as_ref() {
                            Protocol::Choice {
                                role,
                                branches,
                                annotations,
                            } => {
                                assert_eq!(role.name().to_string(), "Bob");
                                assert_eq!(branches.len(), 2);
                                assert_eq!(branches[0].label.to_string(), "Alive");
                                assert_eq!(branches[1].label.to_string(), "Dead");

                                // Check heartbeat annotation
                                assert!(annotations.has_heartbeat());
                                let (interval, on_missing) = annotations.heartbeat().unwrap();
                                assert_eq!(interval, std::time::Duration::from_secs(1));
                                assert_eq!(on_missing, 3);
                            }
                            _ => panic!("Expected Choice as continuation"),
                        }
                    }
                    _ => panic!("Expected Send inside Rec"),
                }
            }
            _ => panic!("Expected Rec as top-level protocol"),
        }
    }

    #[test]
    fn test_parse_heartbeat_milliseconds() {
        let input = r#"
protocol FastHeartbeat =
  roles Client, Server
  heartbeat Client -> Server every 500ms on_missing(5) {
    Server -> Client : Dead
  } body {
    Client -> Server : Ping
  }
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse heartbeat with ms: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Rec { body, .. } => match body.as_ref() {
                Protocol::Send { continuation, .. } => match continuation.as_ref() {
                    Protocol::Choice { annotations, .. } => {
                        assert!(annotations.has_heartbeat());
                        let (interval, on_missing) = annotations.heartbeat().unwrap();
                        assert_eq!(interval, std::time::Duration::from_millis(500));
                        assert_eq!(on_missing, 5);
                    }
                    _ => panic!("Expected Choice"),
                },
                _ => panic!("Expected Send"),
            },
            _ => panic!("Expected Rec"),
        }
    }

    #[test]
    fn test_parse_runtime_timeout_annotation() {
        let input = r#"
protocol TimedRequest =
  roles Client, Server
  @runtime_timeout(5s) Client -> Server : Request
  Server -> Client : Response
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse @runtime_timeout: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send {
                annotations,
                continuation,
                ..
            } => {
                // Check the runtime_timeout annotation was parsed
                assert!(annotations.has_runtime_timeout());
                let timeout = annotations.runtime_timeout().unwrap();
                assert_eq!(timeout, std::time::Duration::from_secs(5));

                // Check continuation doesn't have the annotation
                match continuation.as_ref() {
                    Protocol::Send { annotations, .. } => {
                        assert!(!annotations.has_runtime_timeout());
                    }
                    _ => panic!("Expected Send for Response"),
                }
            }
            _ => panic!("Expected Send for Request"),
        }
    }

    #[test]
    fn test_parse_runtime_timeout_milliseconds() {
        let input = r#"
protocol QuickCheck =
  roles A, B
  @runtime_timeout(100ms) A -> B : Ping
"#;

        let result = parse_choreography_str(input);
        assert!(
            result.is_ok(),
            "Failed to parse @runtime_timeout with ms: {:?}",
            result.err()
        );

        let choreo = result.unwrap();
        match &choreo.protocol {
            Protocol::Send { annotations, .. } => {
                assert!(annotations.has_runtime_timeout());
                let timeout = annotations.runtime_timeout().unwrap();
                assert_eq!(timeout, std::time::Duration::from_millis(100));
            }
            _ => panic!("Expected Send"),
        }
    }
}
