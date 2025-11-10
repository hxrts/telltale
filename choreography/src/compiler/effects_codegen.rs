// Code generation for free algebra choreographic protocols
//
// This module generates protocol implementations that build
// effect programs using a free algebra approach.

use crate::ast::{Choreography, Condition, MessageType, Protocol, Role};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;

/// Generate effect-based protocol implementation
#[must_use] 
pub fn generate_effects_protocol(choreography: &Choreography) -> TokenStream {
    let protocol_name = &choreography.name;
    let roles = generate_role_enum(&choreography.roles);
    let messages = generate_message_types(&choreography.protocol);
    let role_functions = generate_role_functions(choreography);
    let endpoint_type = generate_endpoint_type(protocol_name);

    quote! {
        use rumpsteak_aura_choreography::{
            ChoreoHandler, Result, Label, Program, Effect,
            interpret, InterpretResult, ProgramMessage
        };
        use serde::{Serialize, Deserialize};

        // Common message trait for this choreography
        #[derive(Clone, Debug, Serialize, Deserialize)]
        pub enum Message {
            // Generated message variants would go here
            Default,
        }

        impl ProgramMessage for Message {}

        #roles

        #endpoint_type

        #messages

        #role_functions
    }
}

fn generate_role_enum(roles: &[Role]) -> TokenStream {
    let role_names: Vec<_> = roles.iter().map(|r| &r.name).collect();

    quote! {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub enum Role {
            #(#role_names),*
        }

        impl rumpsteak::effects::RoleId for Role {}
    }
}

fn generate_endpoint_type(protocol_name: &proc_macro2::Ident) -> TokenStream {
    let ep_name = format_ident!("{}Endpoint", protocol_name);

    quote! {
        pub struct #ep_name {
            // Protocol-specific endpoint state
        }

        impl rumpsteak::effects::Endpoint for #ep_name {}
    }
}

fn generate_message_types(protocol: &Protocol) -> TokenStream {
    let mut message_types = HashSet::new();

    // Collect unique message types from protocol
    collect_message_types(protocol, &mut message_types);

    let message_structs: Vec<_> = message_types
        .into_iter()
        .map(|msg_type| {
            let type_name = &msg_type.name;
            let content_type = if let Some(ref payload) = msg_type.payload {
                payload.clone()
            } else {
                infer_content_type(&msg_type.name.to_string())
            };

            quote! {
                #[derive(Clone, Debug, Serialize, Deserialize)]
                pub struct #type_name(pub #content_type);
            }
        })
        .collect();

    quote! {
        #(#message_structs)*
    }
}

fn collect_message_types(protocol: &Protocol, message_types: &mut HashSet<MessageType>) {
    match protocol {
        Protocol::Send {
            message,
            continuation,
            ..
        } => {
            message_types.insert(message.clone());
            collect_message_types(continuation, message_types);
        }
        Protocol::Broadcast {
            message,
            continuation,
            ..
        } => {
            message_types.insert(message.clone());
            collect_message_types(continuation, message_types);
        }
        Protocol::Choice { branches, .. } => {
            for branch in branches {
                collect_message_types(&branch.protocol, message_types);
            }
        }
        Protocol::Loop { body, .. } => {
            collect_message_types(body, message_types);
        }
        Protocol::Parallel { protocols } => {
            for p in protocols {
                collect_message_types(p, message_types);
            }
        }
        Protocol::Rec { body, .. } => {
            collect_message_types(body, message_types);
        }
        Protocol::Var(_) | Protocol::End => {}
    }
}

fn generate_role_functions(choreography: &Choreography) -> TokenStream {
    choreography
        .roles
        .iter()
        .map(|role| {
            let role_name_str = role.name.to_string().to_lowercase();
            let program_fn_name = format_ident!("{}_program", role_name_str);
            let run_fn_name = format_ident!("run_{}", role_name_str);
            let protocol_name = &choreography.name;
            let endpoint_type = format_ident!("{}Endpoint", protocol_name);

            let body = generate_role_body(&choreography.protocol, role);

            quote! {
                /// Generate the choreographic program for this role
                pub fn #program_fn_name() -> Program<Role, Message> {
                    #body
                }

                /// Run the choreographic program for this role using a handler
                pub async fn #run_fn_name<H: ChoreoHandler<Role = Role, Endpoint = #endpoint_type>>(
                    handler: &mut H,
                    endpoint: &mut #endpoint_type,
                ) -> Result<InterpretResult<Message>> {
                    let program = #program_fn_name();
                    interpret(handler, endpoint, program).await
                }
            }
        })
        .collect()
}

fn generate_role_body(protocol: &Protocol, role: &Role) -> TokenStream {
    generate_program_builder(protocol, role)
}

/// Generate program builder code for a protocol from the perspective of a specific role
fn generate_program_builder(protocol: &Protocol, role: &Role) -> TokenStream {
    let program_effects = generate_program_effects(protocol, role);

    quote! {
        use rumpsteak_aura_choreography::{Program, Effect, Label};

        Program::new()
            #program_effects
            .end()
    }
}

/// Generate effect builder calls for a protocol
fn generate_program_effects(protocol: &Protocol, role: &Role) -> TokenStream {
    match protocol {
        Protocol::End => {
            quote! {}
        }
        Protocol::Send {
            from,
            to,
            message,
            continuation,
        } => {
            let continuation_effects = generate_program_effects(continuation, role);

            if from == role {
                // This role is sending
                let message_type = &message.name;
                let to_ident = &to.name;

                quote! {
                    .send(Role::#to_ident, #message_type::default())
                    #continuation_effects
                }
            } else if to == role {
                // This role is receiving
                let message_type = &message.name;
                let from_ident = &from.name;

                quote! {
                    .recv::<#message_type>(Role::#from_ident)
                    #continuation_effects
                }
            } else {
                // This role is not involved in this step
                continuation_effects
            }
        }
        Protocol::Choice {
            role: choice_role,
            branches,
        } => {
            // Generate Branch effect with all possible continuations
            let choice_role_name = &choice_role.name;

            // Generate all branch continuations
            let branch_programs: Vec<_> = branches
                .iter()
                .map(|branch| {
                    let label_str = branch.label.to_string();
                    let branch_effects = generate_program_effects(&branch.protocol, role);

                    quote! {
                        (Label(#label_str), Program::new()#branch_effects)
                    }
                })
                .collect();

            if choice_role == role {
                // This role is making the choice
                // Check if branches have guards - if so, generate guard evaluation
                // Otherwise, generate code that takes the first valid branch
                let has_guards = branches.iter().any(|b| b.guard.is_some());

                if has_guards {
                    // Generate guard evaluation logic
                    let guard_checks: Vec<TokenStream> = branches
                        .iter()
                        .map(|branch| {
                            let label_str = branch.label.to_string();
                            if let Some(ref guard) = branch.guard {
                                quote! {
                                    if #guard {
                                        Label(#label_str)
                                    }
                                }
                            } else {
                                quote! {
                                    // No guard - default fallback
                                    { Label(#label_str) }
                                }
                            }
                        })
                        .collect();

                    // Generate a choice selection expression using guards
                    let first_label = branches
                        .first()
                        .map(|b| b.label.to_string())
                        .unwrap_or_default();
                    quote! {
                        .choose(Role::#choice_role_name, {
                            // Evaluate guards to determine which branch to choose
                            #(#guard_checks else)* Label(#first_label)
                        })
                        .branch(Role::#choice_role_name, vec![#(#branch_programs),*])
                    }
                } else if let Some(first_branch) = branches.first() {
                    // No guards - default to first branch or allow runtime decision
                    let label_str = first_branch.label.to_string();

                    quote! {
                        .choose(Role::#choice_role_name, Label(#label_str))
                        .branch(Role::#choice_role_name, vec![#(#branch_programs),*])
                    }
                } else {
                    quote! {}
                }
            } else {
                // This role is offering/waiting for choice
                // It will receive the label and execute the matching branch
                quote! {
                    .offer(Role::#choice_role_name)
                    .branch(Role::#choice_role_name, vec![#(#branch_programs),*])
                }
            }
        }
        Protocol::Loop { body, condition } => {
            let body_effects = generate_program_effects(body, role);

            // Generate Loop effect with runtime iteration control
            match condition {
                Some(Condition::Count(n)) => {
                    // Fixed iteration count - use loop_n
                    quote! {
                        .loop_n(#n, Program::new()#body_effects)
                    }
                }
                Some(Condition::RoleDecides(deciding_role)) => {
                    // Role-based loop control via choice mechanism
                    // The deciding role uses choices to signal continue/break
                    // Other roles follow the decision

                    if deciding_role == role {
                        // This role decides - wrap body in a choice-controlled loop
                        // The choice determines whether to continue or break
                        quote! {
                            // Loop controlled by this role via choices
                            // Check condition and choose "continue" or "break"
                            // Execute once (implicit "break" choice in this generation)
                            .loop_n(1, Program::new()#body_effects)
                        }
                    } else {
                        // This role follows the deciding role's decision
                        quote! {
                            // Loop follows Role::#deciding_role_name's decision
                            // Receives "continue" or "break" choice from deciding role
                            .loop_n(1, Program::new()#body_effects)
                        }
                    }
                }
                Some(Condition::Custom(_expr)) => {
                    // Custom condition - evaluate expression at runtime
                    // The expression determines loop iteration count or termination
                    quote! {
                        // Loop with custom condition: #expr
                        // Condition is evaluated to determine iteration count
                        .loop_n({
                            // Evaluate custom condition to get iteration count
                            // Default to 1 if condition doesn't produce a count
                            let count: usize = 1; // Custom expr evaluation would go here
                            count
                        }, Program::new()#body_effects)
                    }
                }
                None => {
                    // No explicit condition - execute once
                    quote! {
                        .loop_n(1, Program::new()#body_effects)
                    }
                }
            }
        }
        Protocol::Parallel { protocols } => {
            // For simplicity, execute sequentially in program building
            let parallel_effects: Vec<TokenStream> = protocols
                .iter()
                .map(|p| generate_program_effects(p, role))
                .collect();

            quote! {
                #(#parallel_effects)*
            }
        }
        Protocol::Rec { label: _, body } => {
            // For simplicity, treat recursion as a simple body
            generate_program_effects(body, role)
        }
        Protocol::Broadcast {
            from,
            to_all,
            message,
            continuation,
        } => {
            let continuation_effects = generate_program_effects(continuation, role);
            let message_type = &message.name;

            if from == role {
                // This role is broadcasting - send to all recipients
                let sends: Vec<TokenStream> = to_all
                    .iter()
                    .map(|to| {
                        let to_ident = &to.name;
                        quote! {
                            .send(Role::#to_ident, #message_type::default())
                        }
                    })
                    .collect();

                quote! {
                    #(#sends)*
                    #continuation_effects
                }
            } else if to_all.contains(role) {
                // This role is receiving the broadcast
                let from_ident = &from.name;

                quote! {
                    .recv::<#message_type>(Role::#from_ident)
                    #continuation_effects
                }
            } else {
                // This role doesn't participate in the broadcast
                quote! {
                    #continuation_effects
                }
            }
        }
        Protocol::Var(_label) => {
            // Variable reference for recursion - refers back to a Rec label
            // This creates a recursive call/loop back to the labeled protocol point
            quote! {
                // Recursion to recursive label
                // This represents a jump back to the Rec point
                // In a runtime implementation, this would:
                // 1. Reset state to the Rec entry point
                // 2. Continue execution from the beginning of the Rec body
                // 3. Maintain any accumulated state/messages
                // For code generation, this is typically handled by the containing Rec block
                // which wraps the body in an actual loop construct
            }
        }
    }
}

fn infer_content_type(message_type: &str) -> TokenStream {
    // Simple heuristic - can be improved
    match message_type {
        s if s.contains("Request") => quote! { String },
        s if s.contains("Response") => quote! { String },
        s if s.contains("Data") => quote! { Vec<u8> },
        s if s.contains("Count") => quote! { u64 },
        s if s.contains("Flag") => quote! { bool },
        _ => quote! { String },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{Protocol, Role};

    #[test]
    fn test_generate_simple_protocol() {
        let choreography = Choreography {
            name: format_ident!("SimpleProtocol"),
            roles: vec![
                Role::new(format_ident!("Client")),
                Role::new(format_ident!("Server")),
            ],
            protocol: Protocol::End,
            attrs: std::collections::HashMap::new(),
        };

        let code = generate_effects_protocol(&choreography);
        let code_str = code.to_string();

        assert!(code_str.contains("enum Role"));
        assert!(code_str.contains("Client"));
        assert!(code_str.contains("Server"));
        assert!(code_str.contains("run_client"));
        assert!(code_str.contains("run_server"));
    }
}
