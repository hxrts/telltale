// Code generation for free algebra choreographic protocols
//
// This module generates protocol implementations that build
// effect programs using a free algebra approach.

use crate::ast::{Choreography, Condition, MessageType, Protocol, Role};
use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use std::collections::HashSet;

/// Generate annotation-aware effect metadata for a protocol node
fn generate_effect_metadata_from_annotations(protocol: &Protocol, _role: &Role) -> TokenStream {
    use crate::ast::ProtocolAnnotation;

    let annotations = protocol.get_annotations();

    if annotations.is_empty() {
        return quote! {};
    }

    let metadata_items: Vec<TokenStream> = annotations
        .iter()
        .filter_map(|annotation| {
            match annotation {
                ProtocolAnnotation::Priority(value) => Some(quote! { .with_priority(#value) }),
                ProtocolAnnotation::RuntimeTimeout(dur) => {
                    let secs = dur.as_secs();
                    Some(quote! { .with_timeout(std::time::Duration::from_secs(#secs)) })
                }
                ProtocolAnnotation::Retry { max_attempts, .. } => {
                    Some(quote! { .with_retry(#max_attempts) })
                }
                ProtocolAnnotation::Custom { key, value } => {
                    // Generic annotation - add as metadata
                    Some(quote! { .with_annotation(#key, #value) })
                }
                // Skip annotations that don't generate effect metadata
                // (these are handled elsewhere or are purely structural)
                ProtocolAnnotation::TimedChoice { .. }
                | ProtocolAnnotation::Idempotent
                | ProtocolAnnotation::Trace { .. }
                | ProtocolAnnotation::Heartbeat { .. } => None,
            }
        })
        .collect();

    quote! { #(#metadata_items)* }
}

/// Generate effect-based protocol implementation
#[must_use]
pub fn generate_effects_protocol(choreography: &Choreography) -> TokenStream {
    let protocol_name = &choreography.name;
    let roles = generate_role_enum(&choreography.roles);
    let labels = generate_label_type(&choreography.protocol);
    let messages = generate_message_types(&choreography.protocol);
    let role_functions = generate_role_functions(choreography);
    let endpoint_type = generate_endpoint_type(protocol_name);

    quote! {
        use rumpsteak_aura_choreography::{
            ChoreoHandler, Result, Program, Effect, LabelId, RoleId, RoleName,
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

        #labels

        #messages

        #role_functions
    }
}

fn generate_role_enum(roles: &[Role]) -> TokenStream {
    let role_names: Vec<_> = roles.iter().map(|r| r.name()).collect();
    let role_match_arms = roles.iter().map(|role| {
        let role_name = role.name();
        let role_str = role.name().to_string();
        quote! { Role::#role_name => RoleName::from_static(#role_str) }
    });

    quote! {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub enum Role {
            #(#role_names),*
        }

        impl RoleId for Role {
            type Label = Label;

            fn role_name(&self) -> RoleName {
                match self {
                    #(#role_match_arms),*
                }
            }
        }
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

fn generate_label_type(protocol: &Protocol) -> TokenStream {
    let mut labels = HashSet::new();
    collect_choice_labels(protocol, &mut labels);

    let mut label_list: Vec<String> = labels.into_iter().collect();
    label_list.sort();

    if label_list.is_empty() {
        return quote! {
            #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
            pub enum Label {}

            impl LabelId for Label {
                fn as_str(&self) -> &'static str {
                    match *self {}
                }

                fn from_str(_label: &str) -> Option<Self> {
                    None
                }
            }
        };
    }

    let variants = label_list.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { #ident }
    });

    let as_str_arms = label_list.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { Label::#ident => #label }
    });

    let from_str_arms = label_list.iter().map(|label| {
        let ident = format_ident!("{}", label);
        quote! { #label => Some(Label::#ident) }
    });

    quote! {
        #[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
        pub enum Label {
            #(#variants),*
        }

        impl LabelId for Label {
            fn as_str(&self) -> &'static str {
                match self {
                    #(#as_str_arms),*
                }
            }

            fn from_str(label: &str) -> Option<Self> {
                match label {
                    #(#from_str_arms),*,
                    _ => None,
                }
            }
        }
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

        Protocol::Extension { continuation, .. } => {
            collect_message_types(continuation, message_types);
        }
    }
}

fn collect_choice_labels(protocol: &Protocol, labels: &mut HashSet<String>) {
    match protocol {
        Protocol::Choice { branches, .. } => {
            for branch in branches {
                labels.insert(branch.label.to_string());
                collect_choice_labels(&branch.protocol, labels);
            }
        }
        Protocol::Send { continuation, .. }
        | Protocol::Broadcast { continuation, .. }
        | Protocol::Extension { continuation, .. } => {
            collect_choice_labels(continuation, labels);
        }
        Protocol::Loop { body, .. } | Protocol::Rec { body, .. } => {
            collect_choice_labels(body, labels);
        }
        Protocol::Parallel { protocols } => {
            for proto in protocols {
                collect_choice_labels(proto, labels);
            }
        }
        Protocol::Var(_) | Protocol::End => {}
    }
}

fn generate_role_functions(choreography: &Choreography) -> TokenStream {
    choreography
        .roles
        .iter()
        .map(|role| {
            let role_name_str = role.name().to_string().to_lowercase();
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
        use rumpsteak_aura_choreography::{Program, Effect};

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
            ..
        } => {
            let continuation_effects = generate_program_effects(continuation, role);

            if from == role {
                // This role is sending
                let message_type = &message.name;
                let to_ident = to.name();
                let send_metadata = generate_effect_metadata_from_annotations(protocol, role);

                quote! {
                    .send(Role::#to_ident, #message_type::default())
                    #send_metadata
                    #continuation_effects
                }
            } else if to == role {
                // This role is receiving
                let message_type = &message.name;
                let from_ident = from.name();
                let recv_metadata = generate_effect_metadata_from_annotations(protocol, role);

                quote! {
                    .recv::<#message_type>(Role::#from_ident)
                    #recv_metadata
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
            annotations,
        } => {
            // Check for timed_choice annotation using typed accessor
            let timed_choice_duration = annotations.timed_choice();
            let is_timed_choice = timed_choice_duration.is_some();
            let timeout_ms = timed_choice_duration
                .map(|d| d.as_millis() as u64)
                .unwrap_or(5000); // Default 5 seconds

            // Generate Branch effect with all possible continuations
            let choice_role_name = choice_role.name();

            // Generate all branch continuations
            let branch_programs: Vec<_> = branches
                .iter()
                .map(|branch| {
                    let label_ident = &branch.label;
                    let branch_effects = generate_program_effects(&branch.protocol, role);

                    quote! {
                        (Label::#label_ident, Program::new()#branch_effects.end())
                    }
                })
                .collect();

            if choice_role == role {
                // This role is making the choice
                if is_timed_choice {
                    // For timed choice: the actor races operations against a timeout
                    // The first branch is executed if action completes in time (OnTime)
                    // The second branch is executed if timeout fires first (TimedOut)
                    //
                    // Generated code wraps the choice in a timeout effect:
                    // .with_timeout(duration, normal_program)
                    // The handler will use tokio::select! internally

                    // Find OnTime and TimedOut branches
                    let on_time_branch = branches.iter().find(|b| b.label == "OnTime");
                    let timed_out_branch = branches.iter().find(|b| b.label == "TimedOut");

                    match (on_time_branch, timed_out_branch) {
                        (Some(on_time), Some(timed_out)) => {
                            let on_time_effects = generate_program_effects(&on_time.protocol, role);
                            let timed_out_effects =
                                generate_program_effects(&timed_out.protocol, role);

                            quote! {
                                .with_timed_choice(
                                    Role::#choice_role_name,
                                    std::time::Duration::from_millis(#timeout_ms),
                                    // OnTime branch - executed if no timeout
                                    Program::new()
                                        .choose(Role::#choice_role_name, Label::OnTime)
                                        #on_time_effects
                                        .end(),
                                    // TimedOut branch - executed on timeout
                                    Program::new()
                                        .choose(Role::#choice_role_name, Label::TimedOut)
                                        #timed_out_effects
                                        .end()
                                )
                            }
                        }
                        _ => {
                            // Fall back to regular choice if OnTime/TimedOut not found
                            let first_branch = branches.first();
                            let label_ident = &first_branch.label;
                            quote! {
                                .with_timed_choice(
                                    Role::#choice_role_name,
                                    std::time::Duration::from_millis(#timeout_ms),
                                    Program::new()
                                        .choose(Role::#choice_role_name, Label::#label_ident)
                                        .branch(Role::#choice_role_name, vec![#(#branch_programs),*])
                                        .end(),
                                    // Timeout takes first branch as fallback
                                    Program::new()
                                        .choose(Role::#choice_role_name, Label::#label_ident)
                                        .end()
                                )
                            }
                        }
                    }
                } else {
                    // Standard choice without timeout
                    // Check if branches have guards - if so, generate guard evaluation
                    // Otherwise, generate code that takes the first valid branch
                    let has_guards = branches.iter().any(|b| b.guard.is_some());

                    if has_guards {
                        // Generate guard evaluation logic
                        let guard_checks: Vec<TokenStream> = branches
                            .iter()
                            .map(|branch| {
                                let label_ident = &branch.label;
                                if let Some(ref guard) = branch.guard {
                                    quote! {
                                        if #guard {
                                            Label::#label_ident
                                        }
                                    }
                                } else {
                                    quote! {
                                        // No guard - default fallback
                                        { Label::#label_ident }
                                    }
                                }
                            })
                            .collect();

                        // Generate a choice selection expression using guards
                        let first_label = branches.first();
                        let first_label_ident = &first_label.label;
                        quote! {
                            .choose(Role::#choice_role_name, {
                                // Evaluate guards to determine which branch to choose
                                #(#guard_checks else)* Label::#first_label_ident
                            })
                            .branch(Role::#choice_role_name, vec![#(#branch_programs),*])
                        }
                    } else {
                        // No guards - default to first branch or allow runtime decision
                        let first_branch = branches.first();
                        let label_ident = &first_branch.label;

                        quote! {
                            .choose(Role::#choice_role_name, Label::#label_ident)
                            .branch(Role::#choice_role_name, vec![#(#branch_programs),*])
                        }
                    }
                }
            } else {
                // This role is offering/waiting for choice
                // It will receive the label and execute the matching branch
                if is_timed_choice {
                    // For timed choice receivers: they still wait for the choice
                    // The timeout is managed by the choice maker, so receivers
                    // just offer as normal. They'll receive either OnTime or TimedOut.
                    quote! {
                        .offer(Role::#choice_role_name)
                        .branch(Role::#choice_role_name, vec![#(#branch_programs),*])
                    }
                } else {
                    quote! {
                        .offer(Role::#choice_role_name)
                        .branch(Role::#choice_role_name, vec![#(#branch_programs),*])
                    }
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
                        .loop_n(#n, Program::new()#body_effects.end())
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
                            .loop_n(1, Program::new()#body_effects.end())
                        }
                    } else {
                        // This role follows the deciding role's decision
                        quote! {
                            // Loop follows Role::#deciding_role_name's decision
                            // Receives "continue" or "break" choice from deciding role
                            .loop_n(1, Program::new()#body_effects.end())
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
                        }, Program::new()#body_effects.end())
                    }
                }
                Some(Condition::Fuel(n)) => {
                    // Fuel-based bounding - max iterations
                    quote! {
                        .loop_n(#n, Program::new()#body_effects.end())
                    }
                }
                Some(Condition::YieldAfter(n)) => {
                    // Yield after N communication steps
                    // Execute up to N iterations then yield
                    quote! {
                        .loop_n(#n, Program::new()#body_effects.end())
                    }
                }
                Some(Condition::YieldWhen(_condition)) => {
                    // Yield when condition is met
                    // For now, execute once and check condition
                    quote! {
                        .loop_n(1, Program::new()#body_effects.end())
                    }
                }
                None => {
                    // No explicit condition - execute once
                    quote! {
                        .loop_n(1, Program::new()#body_effects.end())
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
            ..
        } => {
            let continuation_effects = generate_program_effects(continuation, role);
            let message_type = &message.name;

            if from == role {
                // This role is broadcasting - send to all recipients
                let sends: Vec<TokenStream> = to_all
                    .iter()
                    .map(|to| {
                        let to_ident = to.name();
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
                let from_ident = from.name();

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

        Protocol::Extension {
            extension,
            continuation,
            ..
        } => {
            // Generate code for the extension and then continue with the rest
            let extension_effects =
                extension.generate_code(&crate::extensions::CodegenContext::default());
            let continuation_effects = generate_program_effects(continuation, role);

            quote! {
                #extension_effects
                #continuation_effects
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
            namespace: None,
            roles: vec![
                Role::new(format_ident!("Client")).unwrap(),
                Role::new(format_ident!("Server")).unwrap(),
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
