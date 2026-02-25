use super::*;

pub(crate) fn generate_runner_body(
    local_type: &LocalType,
    ctx: &mut RecursionContext,
) -> TokenStream {
    match local_type {
        LocalType::Send {
            to,
            message,
            continuation,
        } => {
            let msg_type = &message.name;
            let cont = generate_runner_body(continuation, ctx);

            // Check if destination is a wildcard or range (multi-destination)
            if let Some(index) = to.index() {
                match index {
                    crate::ast::role::RoleIndex::Wildcard => {
                        // Generate broadcast to all instances of the role family
                        let family_name = to.name().to_string();
                        return quote! {
                            // Broadcast to all #family_name instances
                            let roles = adapter.resolve_family(#family_name)?;
                            if roles.is_empty() {
                                return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                    #family_name.to_string()
                                ).into());
                            }
                            let msg: #msg_type = adapter.provide_message(roles[0]).await?;
                            adapter.broadcast(&roles, msg).await?;
                            #cont
                        };
                    }
                    crate::ast::role::RoleIndex::Range(range) => {
                        // Generate broadcast to a range of role instances
                        let family_name = to.name().to_string();
                        let (start_expr, end_expr) = generate_range_exprs(range);
                        return quote! {
                            // Broadcast to #family_name range
                            let roles = adapter.resolve_range(#family_name, #start_expr, #end_expr)?;
                            if roles.is_empty() {
                                return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                    #family_name.to_string()
                                ).into());
                            }
                            let msg: #msg_type = adapter.provide_message(roles[0]).await?;
                            adapter.broadcast(&roles, msg).await?;
                            #cont
                        };
                    }
                    _ => {} // Fall through to normal send
                }
            }

            // Normal single-destination send
            let to_role = generate_role_id(to);
            quote! {
                // Send to #to
                let msg: #msg_type = adapter.provide_message(#to_role).await?;
                adapter.send(#to_role, msg).await?;
                #cont
            }
        }

        LocalType::Receive {
            from,
            message,
            continuation,
        } => {
            let msg_type = &message.name;
            let cont = generate_runner_body(continuation, ctx);

            // Check if source is a wildcard or range (multi-source collect)
            if let Some(index) = from.index() {
                match index {
                    crate::ast::role::RoleIndex::Wildcard => {
                        // Generate collect from all instances of the role family
                        let family_name = from.name().to_string();
                        return quote! {
                            // Collect from all #family_name instances
                            let roles = adapter.resolve_family(#family_name)?;
                            if roles.is_empty() {
                                return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                    #family_name.to_string()
                                ).into());
                            }
                            let _msgs: Vec<#msg_type> = adapter.collect(&roles).await?;
                            output.metadata.messages_received += _msgs.len();
                            for msg in &_msgs {
                                let value = ::serde_json::to_value(msg).map_err(|e| {
                                    ::telltale_choreography::ChoreographyError::ExecutionError(
                                        e.to_string(),
                                    )
                                })?;
                                output.received.push(value);
                            }
                            #cont
                        };
                    }
                    crate::ast::role::RoleIndex::Range(range) => {
                        // Generate collect from a range of role instances
                        let family_name = from.name().to_string();
                        let (start_expr, end_expr) = generate_range_exprs(range);
                        return quote! {
                            // Collect from #family_name range
                            let roles = adapter.resolve_range(#family_name, #start_expr, #end_expr)?;
                            if roles.is_empty() {
                                return Err(::telltale_choreography::ChoreographyError::EmptyRoleFamily(
                                    #family_name.to_string()
                                ).into());
                            }
                            let _msgs: Vec<#msg_type> = adapter.collect(&roles).await?;
                            output.metadata.messages_received += _msgs.len();
                            for msg in &_msgs {
                                let value = ::serde_json::to_value(msg).map_err(|e| {
                                    ::telltale_choreography::ChoreographyError::ExecutionError(
                                        e.to_string(),
                                    )
                                })?;
                                output.received.push(value);
                            }
                            #cont
                        };
                    }
                    _ => {} // Fall through to normal receive
                }
            }

            // Normal single-source receive
            let from_role = generate_role_id(from);
            quote! {
                // Receive from #from
                let _msg: #msg_type = adapter.recv(#from_role).await?;
                output.metadata.messages_received += 1;
                let value = ::serde_json::to_value(&_msg).map_err(|e| {
                    ::telltale_choreography::ChoreographyError::ExecutionError(e.to_string())
                })?;
                output.received.push(value);
                #cont
            }
        }

        LocalType::Select { to, branches } => {
            let to_role = generate_role_id(to);

            // Generate match arms for each branch
            let match_arms: Vec<TokenStream> = branches
                .iter()
                .map(|(label, cont_type)| {
                    let cont = generate_runner_body(cont_type, ctx);
                    quote! {
                        BranchLabel::#label => {
                            adapter.choose(#to_role, BranchLabel::#label).await?;
                            #cont
                        }
                    }
                })
                .collect();

            let choice_variants: Vec<TokenStream> = branches
                .iter()
                .map(|(label, _)| {
                    quote! { BranchLabel::#label }
                })
                .collect();

            quote! {
                // Internal choice - select branch to send to #to
                let choice = adapter.select_branch(&[#(#choice_variants),*]).await?;
                output.choices.push(choice);
                match choice {
                    #(#match_arms)*
                }
            }
        }

        LocalType::Branch { from, branches } => {
            let from_role = generate_role_id(from);

            // Generate match arms for each branch
            let match_arms: Vec<TokenStream> = branches
                .iter()
                .map(|(label, cont_type)| {
                    let cont = generate_runner_body(cont_type, ctx);
                    quote! {
                        BranchLabel::#label => {
                            #cont
                        }
                    }
                })
                .collect();

            quote! {
                // External choice - receive branch selection from #from
                let label = adapter.offer(#from_role).await?;
                output.choices.push(label);
                match label {
                    #(#match_arms)*
                }
            }
        }

        LocalType::LocalChoice { branches } => {
            // Generate match arms for each branch
            let match_arms: Vec<TokenStream> = branches
                .iter()
                .map(|(label, cont_type)| {
                    let cont = generate_runner_body(cont_type, ctx);
                    quote! {
                        BranchLabel::#label => {
                            #cont
                        }
                    }
                })
                .collect();

            let choice_variants: Vec<TokenStream> = branches
                .iter()
                .map(|(label, _)| {
                    quote! { BranchLabel::#label }
                })
                .collect();

            quote! {
                // Local choice - no communication
                let choice = adapter.select_branch(&[#(#choice_variants),*]).await?;
                output.choices.push(choice);
                match choice {
                    #(#match_arms)*
                }
            }
        }

        LocalType::Loop { condition, body } => {
            let loop_body = generate_runner_body(body, ctx);

            match condition {
                Some(crate::ast::Condition::Count(n)) => {
                    quote! {
                        // Bounded loop (max #n iterations)
                        for _i in 0..#n {
                            #loop_body
                        }
                    }
                }
                Some(crate::ast::Condition::RoleDecides(role)) => {
                    // Note: RoleDecides loops are normally desugared to choice+rec at parse time.
                    // This case is only reached if someone constructs a LocalType::Loop with
                    // RoleDecides directly, bypassing the normal parse/desugar path.
                    let role_str = role.name().to_string();
                    quote! {
                        return Err(::telltale_choreography::ChoreographyError::ExecutionError(
                            format!(
                                "role-decided loops are not supported directly in generated runners. \
                                 The parser should desugar 'loop decide by {}' to a choice+rec pattern. \
                                 If you see this error, the LocalType was constructed without going \
                                 through the normal parse path.",
                                #role_str
                            )
                        ).into());
                    }
                }
                Some(crate::ast::Condition::Custom(expr)) => {
                    quote! {
                        // Loop with custom condition
                        while #expr {
                            #loop_body
                        }
                    }
                }
                Some(crate::ast::Condition::Fuel(n)) => {
                    quote! {
                        // Fuel-bounded loop (max #n iterations)
                        for _fuel in 0..#n {
                            #loop_body
                        }
                    }
                }
                Some(crate::ast::Condition::YieldAfter(n)) => {
                    quote! {
                        // Yield-after-N loop (max #n steps then yield)
                        for _step in 0..#n {
                            #loop_body
                        }
                        // Yield control after N steps
                    }
                }
                Some(crate::ast::Condition::YieldWhen(condition)) => {
                    quote! {
                        // Yield-when loop - INVARIANT: always breaks after one iteration
                        loop {
                            #loop_body
                            // Check yield condition
                            let _condition = #condition;
                            break; // Yield when condition met
                        }
                    }
                }
                None => {
                    quote! {
                        return Err(::telltale_choreography::ChoreographyError::ExecutionError(
                            "unbounded loops are not supported in generated runners. \
                             Use a bounded loop condition like: \
                             'loop decide by Role' (desugars to choice), \
                             'loop repeat N' (fixed iterations), \
                             'loop fuel N' (max iterations), or \
                             'loop yield_after N' (bounded steps)".to_string()
                        ).into());
                    }
                }
            }
        }

        LocalType::Rec { label, body } => {
            let label_str = label.to_string();

            // Track recursion
            ctx.enter_rec(&label_str);
            let rec_body = generate_runner_body(body, ctx);
            ctx.exit_rec();

            let loop_label = syn::Lifetime::new(
                &format!("'rec_{}", label_str),
                proc_macro2::Span::call_site(),
            );

            quote! {
                // Recursive type
                #loop_label: loop {
                    #rec_body
                    break #loop_label;
                }
            }
        }

        LocalType::Var(label) => {
            let label_str = label.to_string();
            let loop_label = syn::Lifetime::new(
                &format!("'rec_{}", label_str),
                proc_macro2::Span::call_site(),
            );

            if ctx.is_in_rec(&label_str) {
                quote! {
                    // Continue recursive loop
                    continue #loop_label;
                }
            } else {
                quote! {
                    // Recursive variable (unbound) - this indicates a code generator bug
                    // The variable should have been bound by a Mu construct
                    return Err(::telltale_choreography::ChoreographyError::ExecutionError(
                        format!(
                            "unbound recursive variable '{}'; this indicates a code generator bug",
                            #label_str
                        )
                    ).into());
                }
            }
        }

        LocalType::Timeout { duration, body } => {
            let timeout_ms = duration.as_millis() as u64;
            let timeout_body = generate_runner_body(body, ctx);

            quote! {
                // Timeout after #duration ms
                let timeout_result = tokio::time::timeout(
                    std::time::Duration::from_millis(#timeout_ms),
                    async {
                        #timeout_body
                        Ok::<_, A::Error>(())
                    }
                ).await;

                match timeout_result {
                    Ok(inner_result) => inner_result?,
                    Err(_elapsed) => {
                        return Err(::telltale_choreography::ChoreographyError::Timeout(
                            std::time::Duration::from_millis(#timeout_ms),
                        )
                        .into());
                    }
                }
            }
        }

        LocalType::End => {
            quote! {
                // End of protocol
            }
        }
    }
}
