// Parser for choreographic protocol syntax
//
// Full implementation using Pest grammar for parsing choreographic DSL

use crate::ast::{Branch, Choreography, Condition, MessageType, Protocol, Role};
use pest::Parser;
use pest_derive::Parser;
use proc_macro2::{Ident, Span, TokenStream};
use quote::format_ident;
use std::collections::{HashMap, HashSet};
use syn::Result;
use thiserror::Error;

#[derive(Parser)]
#[grammar = "compiler/choreography.pest"]
struct ChoreographyParser;

/// Span information for error reporting
#[derive(Debug, Clone)]
pub struct ErrorSpan {
    pub line: usize,
    pub column: usize,
    pub line_end: usize,
    pub column_end: usize,
    pub snippet: String,
}

impl ErrorSpan {
    /// Create an ErrorSpan from a Pest span
    fn from_pest_span(span: pest::Span, input: &str) -> Self {
        let (line, column) = span.start_pos().line_col();
        let (line_end, column_end) = span.end_pos().line_col();

        // Extract the line containing the error
        let snippet = input.lines().nth(line - 1).unwrap_or("").to_string();

        Self {
            line,
            column,
            line_end,
            column_end,
            snippet,
        }
    }

    /// Format the error with context
    pub fn format_error(&self, message: &str) -> String {
        let line_num_width = self.line.to_string().len().max(3);
        let mut output = String::new();

        // Error message
        output.push_str(&format!("\n{}\n", message));

        // Location
        output.push_str(&format!(
            "  {} {}:{}:{}\n",
            "-->", "input", self.line, self.column
        ));

        // Empty line
        output.push_str(&format!("{:width$} |\n", " ", width = line_num_width));

        // Source line with line number
        output.push_str(&format!(
            "{:>width$} | {}\n",
            self.line,
            self.snippet,
            width = line_num_width
        ));

        // Underline indicator
        let spaces = " ".repeat(line_num_width + 3 + self.column - 1);
        let underline_len = if self.line == self.line_end {
            (self.column_end - self.column).max(1)
        } else {
            self.snippet.len() - self.column + 1
        };
        let underline = "^".repeat(underline_len);
        output.push_str(&format!("{}{}\n", spaces, underline));

        output
    }
}

/// Parse errors that can occur during choreography parsing
#[derive(Error, Debug)]
pub enum ParseError {
    #[error("{}", format_pest_error(.0))]
    Pest(#[from] Box<pest::error::Error<Rule>>),

    #[error("{}", .span.format_error(&format!("Syntax error: {}", .message)))]
    Syntax { span: ErrorSpan, message: String },

    #[error("{}", .span.format_error(&format!("Undefined role '{}'", .role)))]
    UndefinedRole { role: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Duplicate role declaration '{}'", .role)))]
    DuplicateRole { role: String, span: ErrorSpan },

    #[error("Empty choreography: no statements found")]
    EmptyChoreography,

    #[error("{}", .span.format_error(&format!("Invalid message format: {}", .message)))]
    InvalidMessage { message: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Invalid condition: {}", .message)))]
    InvalidCondition { message: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Undefined protocol '{}'", .protocol)))]
    UndefinedProtocol { protocol: String, span: ErrorSpan },

    #[error("{}", .span.format_error(&format!("Duplicate protocol definition '{}'", .protocol)))]
    DuplicateProtocol { protocol: String, span: ErrorSpan },
}

/// Format Pest errors nicely
fn format_pest_error(err: &pest::error::Error<Rule>) -> String {
    format!("\nParse error:\n{}", err)
}

/// Parse an annotation into a key-value pair
fn parse_annotation(
    pair: pest::iterators::Pair<Rule>,
) -> std::result::Result<(String, String), ParseError> {
    let mut key = String::new();
    let mut values = Vec::new();

    for inner in pair.into_inner() {
        match inner.as_rule() {
            Rule::ident => {
                if key.is_empty() {
                    key = inner.as_str().to_string();
                } else {
                    values.push(inner.as_str().to_string());
                }
            }
            Rule::annotation_args => {
                for arg in inner.into_inner() {
                    if let Rule::annotation_arg_list = arg.as_rule() {
                        for arg_item in arg.into_inner() {
                            if let Rule::annotation_arg = arg_item.as_rule() {
                                let mut arg_key = String::new();
                                let mut arg_val = String::new();
                                for part in arg_item.into_inner() {
                                    match part.as_rule() {
                                        Rule::ident => {
                                            if arg_key.is_empty() {
                                                arg_key = part.as_str().to_string();
                                            } else {
                                                arg_val = part.as_str().to_string();
                                            }
                                        }
                                        Rule::annotation_value => {
                                            arg_val = part.as_str().trim_matches('"').to_string();
                                        }
                                        Rule::string => {
                                            arg_val = part.as_str().trim_matches('"').to_string();
                                        }
                                        Rule::integer => {
                                            arg_val = part.as_str().to_string();
                                        }
                                        _ => {}
                                    }
                                }
                                if !arg_val.is_empty() {
                                    values.push(format!("{}={}", arg_key, arg_val));
                                } else if !arg_key.is_empty() {
                                    values.push(arg_key);
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }

    let value = if values.is_empty() {
        "true".to_string()
    } else {
        values.join(",")
    };

    Ok((key, value))
}

/// Parse a choreographic protocol from a string
pub fn parse_choreography_str(input: &str) -> std::result::Result<Choreography, ParseError> {
    let pairs = ChoreographyParser::parse(Rule::choreography, input).map_err(Box::new)?;

    let mut name = format_ident!("Unnamed");
    let mut roles = Vec::new();
    let mut declared_roles = HashSet::new();
    let mut protocol_defs: HashMap<String, Vec<Statement>> = HashMap::new();
    let mut statements = Vec::new();
    let mut attrs: HashMap<String, String> = HashMap::new();

    for pair in pairs {
        if pair.as_rule() == Rule::choreography {
            for inner in pair.into_inner() {
                match inner.as_rule() {
                    Rule::annotation => {
                        // Parse annotation and add to attrs
                        let (key, value) = parse_annotation(inner)?;
                        attrs.insert(key, value);
                    }
                    Rule::ident => {
                        name = format_ident!("{}", inner.as_str());
                    }
                    Rule::roles_decl => {
                        for role_pair in inner.into_inner() {
                            if let Rule::role_list = role_pair.as_rule() {
                                for role_decl in role_pair.into_inner() {
                                    if let Rule::role_decl = role_decl.as_rule() {
                                        let mut inner_role = role_decl.into_inner();
                                        let role_ident = inner_role.next().unwrap();
                                        let role_name = role_ident.as_str();
                                        let span = role_ident.as_span();

                                        // Check for role parameter
                                        let role = if let Some(param_pair) = inner_role.next() {
                                            if param_pair.as_rule() == Rule::role_param {
                                                // Parse the parameter
                                                let param_str = param_pair.as_str();
                                                let param_str = param_str
                                                    .trim_start_matches('[')
                                                    .trim_end_matches(']');

                                                // Try to parse as integer for array size
                                                if let Ok(size) = param_str.parse::<usize>() {
                                                    Role::array(
                                                        format_ident!("{}", role_name),
                                                        size,
                                                    )
                                                } else {
                                                    // Parse as symbolic parameter
                                                    if let Ok(param_ts) =
                                                        syn::parse_str::<TokenStream>(param_str)
                                                    {
                                                        Role::parameterized(
                                                            format_ident!("{}", role_name),
                                                            param_ts,
                                                        )
                                                    } else {
                                                        return Err(ParseError::Syntax {
                                                            span: ErrorSpan::from_pest_span(
                                                                span, input,
                                                            ),
                                                            message: format!(
                                                                "Invalid role parameter: {}",
                                                                param_str
                                                            ),
                                                        });
                                                    }
                                                }
                                            } else {
                                                Role::new(format_ident!("{}", role_name))
                                            }
                                        } else {
                                            Role::new(format_ident!("{}", role_name))
                                        };

                                        if !declared_roles.insert(role_name.to_string()) {
                                            return Err(ParseError::DuplicateRole {
                                                role: role_name.to_string(),
                                                span: ErrorSpan::from_pest_span(span, input),
                                            });
                                        }
                                        roles.push(role);
                                    }
                                }
                            }
                        }
                    }
                    Rule::protocol_defs => {
                        for protocol_def in inner.into_inner() {
                            if let Rule::protocol_def = protocol_def.as_rule() {
                                let mut def_inner = protocol_def.into_inner();
                                let proto_name_pair = def_inner.next().unwrap();
                                let proto_name = proto_name_pair.as_str();
                                let proto_span = proto_name_pair.as_span();

                                if protocol_defs.contains_key(proto_name) {
                                    return Err(ParseError::DuplicateProtocol {
                                        protocol: proto_name.to_string(),
                                        span: ErrorSpan::from_pest_span(proto_span, input),
                                    });
                                }

                                let body_pair = def_inner.next().unwrap();
                                let body = parse_protocol_body(
                                    body_pair,
                                    &declared_roles,
                                    input,
                                    &protocol_defs,
                                )?;
                                protocol_defs.insert(proto_name.to_string(), body);
                            }
                        }
                    }
                    Rule::protocol_body => {
                        statements =
                            parse_protocol_body(inner, &declared_roles, input, &protocol_defs)?;
                    }
                    Rule::EOI => {}
                    _ => {}
                }
            }
        }
    }

    if roles.is_empty() {
        return Err(ParseError::EmptyChoreography);
    }

    let protocol = convert_statements_to_protocol(&statements, &roles);

    Ok(Choreography {
        name,
        roles,
        protocol,
        attrs,
    })
}

/// Parse protocol body into statements
fn parse_protocol_body(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Vec<Statement>, ParseError> {
    let mut statements = Vec::new();

    for statement_pair in pair.into_inner() {
        let statement = parse_statement(statement_pair, declared_roles, input, protocol_defs)?;
        statements.push(statement);
    }

    Ok(statements)
}

/// Parse a single statement
fn parse_statement(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    // Handle annotated statements
    if let Rule::annotated_stmt = pair.as_rule() {
        let mut inner = pair.into_inner();
        // Skip annotations for now (they're parsed but not stored on individual statements)
        let mut stmt_pair = inner.next().unwrap();
        while stmt_pair.as_rule() == Rule::annotation {
            stmt_pair = inner.next().unwrap();
        }
        return parse_statement_inner(stmt_pair, declared_roles, input, protocol_defs);
    }

    parse_statement_inner(pair, declared_roles, input, protocol_defs)
}

/// Parse the actual statement (without annotations)
fn parse_statement_inner(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    match pair.as_rule() {
        Rule::send_stmt => parse_send_stmt(pair, declared_roles, input),
        Rule::broadcast_stmt => parse_broadcast_stmt(pair, declared_roles, input),
        Rule::choice_stmt => parse_choice_stmt(pair, declared_roles, input, protocol_defs),
        Rule::loop_stmt => parse_loop_stmt(pair, declared_roles, input, protocol_defs),
        Rule::parallel_stmt => parse_parallel_stmt(pair, declared_roles, input, protocol_defs),
        Rule::rec_stmt => parse_rec_stmt(pair, declared_roles, input, protocol_defs),
        Rule::call_stmt => parse_call_stmt(pair, declared_roles, input, protocol_defs),
        _ => {
            let span = pair.as_span();
            Err(ParseError::Syntax {
                span: ErrorSpan::from_pest_span(span, input),
                message: format!("Unexpected statement type: {:?}", pair.as_rule()),
            })
        }
    }
}

/// Parse a role reference (e.g., A, Worker[0], Worker[i])
fn parse_role_ref(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Role, ParseError> {
    let span = pair.as_span();
    let mut inner = pair.into_inner();

    let role_ident = inner.next().unwrap();
    let role_name = role_ident.as_str();

    // Check if the base role name is declared
    if !declared_roles.contains(role_name) {
        return Err(ParseError::UndefinedRole {
            role: role_name.to_string(),
            span: ErrorSpan::from_pest_span(span, input),
        });
    }

    // Check if there's an index
    if let Some(index_pair) = inner.next() {
        if index_pair.as_rule() == Rule::role_index {
            let index_str = index_pair.as_str();
            let index_str = index_str.trim_start_matches('[').trim_end_matches(']');

            // Try to parse as a concrete number
            if let Ok(index) = index_str.parse::<usize>() {
                // Concrete index like Worker[0]
                return Ok(Role {
                    name: format_ident!("{}", role_name),
                    index: Some(index),
                    param: None,
                    array_size: None,
                });
            } else {
                // Symbolic parameter like Worker[i] or Worker[N]
                let param_tokens: TokenStream = index_str.parse().unwrap_or_else(|_| {
                    quote::quote! { #index_str }
                });
                return Ok(Role {
                    name: format_ident!("{}", role_name),
                    index: None,
                    param: Some(param_tokens.clone()),
                    array_size: None,
                });
            }
        }
    }

    // Simple role without index
    Ok(Role::new(format_ident!("{}", role_name)))
}

/// Parse send statement: A -> B: Message(payload)
fn parse_send_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let from_pair = inner.next().unwrap();
    let from = parse_role_ref(from_pair, declared_roles, input)?;

    let to_pair = inner.next().unwrap();
    let to = parse_role_ref(to_pair, declared_roles, input)?;

    let message = parse_message(inner.next().unwrap(), input)?;

    Ok(Statement::Send { from, to, message })
}

/// Parse broadcast statement: A ->* : Message(payload)
fn parse_broadcast_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let from_pair = inner.next().unwrap();
    let from = parse_role_ref(from_pair, declared_roles, input)?;

    let message = parse_message(inner.next().unwrap(), input)?;

    Ok(Statement::Broadcast { from, message })
}

/// Parse choice statement
fn parse_choice_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let role_pair = inner.next().unwrap();
    let role = if role_pair.as_rule() == Rule::ident {
        // Simple identifier without indexing
        let role_name = role_pair.as_str();
        let role_span = role_pair.as_span();
        if !declared_roles.contains(role_name) {
            return Err(ParseError::UndefinedRole {
                role: role_name.to_string(),
                span: ErrorSpan::from_pest_span(role_span, input),
            });
        }
        Role::new(format_ident!("{}", role_name))
    } else {
        // Role reference (potentially with indexing)
        parse_role_ref(role_pair, declared_roles, input)?
    };

    let mut branches = Vec::new();
    for branch_pair in inner {
        if let Rule::choice_branch = branch_pair.as_rule() {
            let mut branch_inner = branch_pair.into_inner();
            let label = format_ident!("{}", branch_inner.next().unwrap().as_str());

            // Check for optional guard
            let mut guard = None;
            let next_item = branch_inner.next().unwrap();
            let body = if let Rule::guard = next_item.as_rule() {
                // Parse guard expression
                let guard_span = next_item.as_span();
                let mut guard_inner = next_item.into_inner();
                let guard_expr = guard_inner.next().unwrap().as_str();
                guard = Some(syn::parse_str::<TokenStream>(guard_expr).map_err(|e| {
                    ParseError::Syntax {
                        span: ErrorSpan::from_pest_span(guard_span, input),
                        message: format!("Invalid guard expression: {}", e),
                    }
                })?);
                // Body comes after guard
                parse_protocol_body(
                    branch_inner.next().unwrap(),
                    declared_roles,
                    input,
                    protocol_defs,
                )?
            } else {
                // No guard, next_item is the body
                parse_protocol_body(next_item, declared_roles, input, protocol_defs)?
            };

            branches.push(ChoiceBranch {
                label,
                guard,
                statements: body,
            });
        }
    }

    Ok(Statement::Choice { role, branches })
}

/// Parse loop statement
fn parse_loop_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let inner = pair.into_inner();

    let mut condition = None;
    let mut body = Vec::new();

    for item in inner {
        match item.as_rule() {
            Rule::count_condition => {
                let span = item.as_span();
                let mut cond_inner = item.into_inner();
                let count_pair = cond_inner.next().unwrap();
                let count_str = count_pair.as_str();

                // Try to parse as integer, otherwise treat as variable
                if let Ok(count) = count_str.parse::<usize>() {
                    condition = Some(Condition::Count(count));
                } else {
                    // Parse as TokenStream for symbolic count
                    let token_stream = syn::parse_str::<TokenStream>(count_str).map_err(|e| {
                        ParseError::InvalidCondition {
                            message: format!("Invalid count: {}", e),
                            span: ErrorSpan::from_pest_span(span, input),
                        }
                    })?;
                    condition = Some(Condition::Custom(token_stream));
                }
            }
            Rule::role_decides_condition => {
                let mut cond_inner = item.into_inner();
                let role_pair = cond_inner.next().unwrap();
                let role_str = role_pair.as_str();
                let role_span = role_pair.as_span();
                if !declared_roles.contains(role_str) {
                    return Err(ParseError::UndefinedRole {
                        role: role_str.to_string(),
                        span: ErrorSpan::from_pest_span(role_span, input),
                    });
                }
                condition = Some(Condition::RoleDecides(Role::new(format_ident!(
                    "{}", role_str
                ))));
            }
            Rule::custom_condition => {
                let span = item.as_span();
                let mut cond_inner = item.into_inner();
                let custom_str = cond_inner.next().unwrap().as_str();
                // Remove quotes from string
                let custom_str = custom_str.trim_matches('"');
                // Parse as TokenStream for Custom condition
                let token_stream = syn::parse_str::<TokenStream>(custom_str).map_err(|e| {
                    ParseError::InvalidCondition {
                        message: format!("Invalid custom condition: {}", e),
                        span: ErrorSpan::from_pest_span(span, input),
                    }
                })?;
                condition = Some(Condition::Custom(token_stream));
            }
            Rule::protocol_body => {
                body = parse_protocol_body(item, declared_roles, input, protocol_defs)?;
            }
            _ => {}
        }
    }

    Ok(Statement::Loop { condition, body })
}

/// Parse parallel statement
fn parse_parallel_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut branches = Vec::new();

    for branch_pair in pair.into_inner() {
        if let Rule::parallel_branch = branch_pair.as_rule() {
            for body_pair in branch_pair.into_inner() {
                if let Rule::protocol_body = body_pair.as_rule() {
                    let body =
                        parse_protocol_body(body_pair, declared_roles, input, protocol_defs)?;
                    branches.push(body);
                }
            }
        }
    }

    Ok(Statement::Parallel { branches })
}

/// Parse recursive statement
fn parse_rec_stmt(
    pair: pest::iterators::Pair<Rule>,
    declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();

    let label = format_ident!("{}", inner.next().unwrap().as_str());
    let body = parse_protocol_body(inner.next().unwrap(), declared_roles, input, protocol_defs)?;

    Ok(Statement::Rec { label, body })
}

/// Parse protocol call statement
fn parse_call_stmt(
    pair: pest::iterators::Pair<Rule>,
    _declared_roles: &HashSet<String>,
    input: &str,
    protocol_defs: &HashMap<String, Vec<Statement>>,
) -> std::result::Result<Statement, ParseError> {
    let mut inner = pair.into_inner();
    let proto_name_pair = inner.next().unwrap();
    let proto_name = proto_name_pair.as_str();
    let span = proto_name_pair.as_span();

    // Look up the protocol definition
    let proto_statements =
        protocol_defs
            .get(proto_name)
            .ok_or_else(|| ParseError::UndefinedProtocol {
                protocol: proto_name.to_string(),
                span: ErrorSpan::from_pest_span(span, input),
            })?;

    // Return a Call statement that will be inlined later
    Ok(Statement::Call {
        name: format_ident!("{}", proto_name),
        statements: proto_statements.clone(),
    })
}

/// Parse message specification
fn parse_message(
    pair: pest::iterators::Pair<Rule>,
    _input: &str,
) -> std::result::Result<MessageSpec, ParseError> {
    let _span = pair.as_span();
    let mut inner = pair.into_inner();

    let name = format_ident!("{}", inner.next().unwrap().as_str());

    let mut type_annotation = None;
    let mut payload = None;

    for part in inner {
        match part.as_rule() {
            Rule::message_type => {
                // Parse the type annotation
                let type_str = part.as_str();
                // Remove angle brackets
                let type_str = type_str.trim_start_matches('<').trim_end_matches('>');
                type_annotation = syn::parse_str::<TokenStream>(type_str).ok();
            }
            Rule::payload => {
                // Parse the payload
                let payload_str = part.as_str();
                let payload_str = payload_str.trim_matches('(').trim_matches(')');
                payload = syn::parse_str::<TokenStream>(payload_str).ok();
            }
            _ => {}
        }
    }

    Ok(MessageSpec {
        name,
        type_annotation,
        payload,
    })
}

/// Choreography statement types
#[derive(Debug, Clone)]
enum Statement {
    Send {
        from: Role,
        to: Role,
        message: MessageSpec,
    },
    Broadcast {
        from: Role,
        message: MessageSpec,
    },
    Choice {
        role: Role,
        branches: Vec<ChoiceBranch>,
    },
    Loop {
        condition: Option<Condition>,
        body: Vec<Statement>,
    },
    Parallel {
        branches: Vec<Vec<Statement>>,
    },
    Rec {
        label: Ident,
        body: Vec<Statement>,
    },
    Call {
        #[allow(dead_code)]
        name: Ident,
        statements: Vec<Statement>,
    },
}

/// Choice branch in choreography
#[derive(Debug, Clone)]
struct ChoiceBranch {
    label: Ident,
    guard: Option<TokenStream>,
    statements: Vec<Statement>,
}

/// Message specification with optional payload
#[derive(Debug, Clone)]
struct MessageSpec {
    name: Ident,
    type_annotation: Option<TokenStream>,
    payload: Option<TokenStream>,
}

/// Convert statements to protocol AST
fn convert_statements_to_protocol(statements: &[Statement], roles: &[Role]) -> Protocol {
    if statements.is_empty() {
        return Protocol::End;
    }

    // First, inline all Call statements
    let inlined = inline_calls(statements);

    let mut current = Protocol::End;

    // Build protocol from back to front
    for statement in inlined.iter().rev() {
        current = match statement {
            Statement::Send { from, to, message } => Protocol::Send {
                from: from.clone(),
                to: to.clone(),
                message: MessageType {
                    name: message.name.clone(),
                    type_annotation: message.type_annotation.clone(),
                    payload: message.payload.clone(),
                },
                continuation: Box::new(current),
            },
            Statement::Broadcast { from, message } => {
                // Resolve to all roles except the sender
                let to_all = roles
                    .iter()
                    .filter(|r| r.name != from.name)
                    .cloned()
                    .collect();

                Protocol::Broadcast {
                    from: from.clone(),
                    to_all,
                    message: MessageType {
                        name: message.name.clone(),
                        type_annotation: message.type_annotation.clone(),
                        payload: message.payload.clone(),
                    },
                    continuation: Box::new(current),
                }
            }
            Statement::Choice { role, branches } => Protocol::Choice {
                role: role.clone(),
                branches: branches
                    .iter()
                    .map(|b| Branch {
                        label: b.label.clone(),
                        guard: b.guard.clone(),
                        protocol: convert_statements_to_protocol(&b.statements, roles),
                    })
                    .collect(),
            },
            Statement::Loop { condition, body } => Protocol::Loop {
                condition: condition.clone(),
                body: Box::new(convert_statements_to_protocol(body, roles)),
            },
            Statement::Parallel { branches } => Protocol::Parallel {
                protocols: branches
                    .iter()
                    .map(|b| convert_statements_to_protocol(b, roles))
                    .collect(),
            },
            Statement::Rec { label, body } => Protocol::Rec {
                label: label.clone(),
                body: Box::new(convert_statements_to_protocol(body, roles)),
            },
            Statement::Call { .. } => {
                // This should not happen after inlining
                current
            }
        };
    }

    current
}

/// Inline all Call statements by replacing them with their definitions
fn inline_calls(statements: &[Statement]) -> Vec<Statement> {
    let mut result = Vec::new();

    for statement in statements {
        match statement {
            Statement::Call { statements, .. } => {
                // Recursively inline the called protocol's statements
                result.extend(inline_calls(statements));
            }
            Statement::Choice { role, branches } => {
                // Inline calls within choice branches
                let new_branches = branches
                    .iter()
                    .map(|b| ChoiceBranch {
                        label: b.label.clone(),
                        guard: b.guard.clone(),
                        statements: inline_calls(&b.statements),
                    })
                    .collect();
                result.push(Statement::Choice {
                    role: role.clone(),
                    branches: new_branches,
                });
            }
            Statement::Loop { condition, body } => {
                // Inline calls within loop body
                result.push(Statement::Loop {
                    condition: condition.clone(),
                    body: inline_calls(body),
                });
            }
            Statement::Parallel { branches } => {
                // Inline calls within parallel branches
                let new_branches = branches.iter().map(|b| inline_calls(b)).collect();
                result.push(Statement::Parallel {
                    branches: new_branches,
                });
            }
            Statement::Rec { label, body } => {
                // Inline calls within recursive body
                result.push(Statement::Rec {
                    label: label.clone(),
                    body: inline_calls(body),
                });
            }
            _ => {
                // Other statements remain unchanged
                result.push(statement.clone());
            }
        }
    }

    result
}

/// Parse a choreographic protocol from a token stream (for macro use)
/// This is a compatibility function that wraps the string parser
pub fn parse_choreography(input: TokenStream) -> Result<Choreography> {
    use syn::LitStr;

    // Try to parse as a string literal (for DSL syntax)
    if let Ok(lit_str) = syn::parse2::<LitStr>(input.clone()) {
        // Parse the DSL string
        let dsl_content = lit_str.value();
        return parse_choreography_str(&dsl_content).map_err(|e| {
            syn::Error::new(lit_str.span(), format!("Choreography parse error: {}", e))
        });
    }

    // If not a string literal, return an error with helpful message
    Err(syn::Error::new(
        proc_macro2::Span::call_site(),
        "choreography! macro expects a string literal containing the choreography DSL.\n\
         Example usage:\n\
         choreography! { r#\"\n\
         choreography MyProtocol {\n\
             roles: Alice, Bob\n\
             Alice -> Bob: Hello\n\
         }\n\
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

    // Generate code
    super::codegen::generate_choreography_code(
        &choreography.name.to_string(),
        &choreography.roles,
        &local_types,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_send() {
        let input = r#"
choreography SimpleSend {
    roles: Alice, Bob

    Alice -> Bob: Hello
}
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
choreography Negotiation {
    roles: Buyer, Seller

    Buyer -> Seller: Offer

    choice Seller {
        accept: {
            Seller -> Buyer: Accept
        }
        reject: {
            Seller -> Buyer: Reject
        }
    }
}
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());

        let choreo = result.unwrap();
        assert_eq!(choreo.name.to_string(), "Negotiation");
    }

    #[test]
    fn test_parse_undefined_role() {
        let input = r#"
choreography Invalid {
    roles: Alice

    Alice -> Bob: Hello
}
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
choreography Invalid {
    roles: Alice, Bob, Alice

    Alice -> Bob: Hello
}
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
    fn test_parse_loop() {
        let input = r#"
choreography LoopProtocol {
    roles: Client, Server

    loop (count: 3) {
        Client -> Server: Request
        Server -> Client: Response
    }
}
"#;

        let result = parse_choreography_str(input);
        assert!(result.is_ok(), "Failed to parse: {:?}", result.err());
    }
}
