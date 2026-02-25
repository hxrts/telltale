    use super::*;
    use crate::ast::Role;

    fn make_role(name: &str) -> Role {
        Role::new(format_ident!("{}", name)).unwrap()
    }

    #[test]
    fn test_generate_role_id_static() {
        let role = make_role("Client");
        let tokens = generate_role_id(&role);
        let expected = quote! { Role::Client };
        assert_eq!(tokens.to_string(), expected.to_string());
    }

    #[test]
    fn test_generate_output_types() {
        let roles = vec![make_role("Client"), make_role("Server")];
        let tokens = generate_output_types(&roles);

        let output = tokens.to_string();
        assert!(output.contains("ClientOutput"));
        assert!(output.contains("ServerOutput"));
    }

    #[test]
    fn test_generate_runner_body_send_wildcard() {
        use crate::ast::{role::RoleIndex, LocalType, MessageType};

        // Create a role with wildcard index: Worker[*]
        let worker = Role::with_index(format_ident!("Worker"), RoleIndex::Wildcard).unwrap();
        let msg = MessageType {
            name: format_ident!("Task"),
            type_annotation: None,
            payload: None,
        };
        let local_type = LocalType::Send {
            to: worker,
            message: msg,
            continuation: Box::new(LocalType::End),
        };

        let tokens = generate_runner_body(&local_type, &mut RecursionContext::new());
        let output = tokens.to_string();

        // Check that we generate resolve_family and broadcast calls
        assert!(
            output.contains("resolve_family"),
            "Should use resolve_family for wildcard"
        );
        assert!(
            output.contains("broadcast"),
            "Should use broadcast for wildcard send"
        );
    }

    #[test]
    fn test_generate_runner_body_send_range() {
        use crate::ast::{
            role::{RangeExpr, RoleIndex, RoleRange},
            LocalType, MessageType,
        };

        // Create a role with range index: Worker[0..3]
        let range = RoleRange {
            start: RangeExpr::Concrete(0),
            end: RangeExpr::Concrete(3),
        };
        let worker = Role::with_index(format_ident!("Worker"), RoleIndex::Range(range)).unwrap();
        let msg = MessageType {
            name: format_ident!("Task"),
            type_annotation: None,
            payload: None,
        };
        let local_type = LocalType::Send {
            to: worker,
            message: msg,
            continuation: Box::new(LocalType::End),
        };

        let tokens = generate_runner_body(&local_type, &mut RecursionContext::new());
        let output = tokens.to_string();

        // Check that we generate resolve_range and broadcast calls
        assert!(
            output.contains("resolve_range"),
            "Should use resolve_range for range"
        );
        assert!(
            output.contains("broadcast"),
            "Should use broadcast for range send"
        );
    }

    #[test]
    fn test_generate_runner_body_recv_wildcard() {
        use crate::ast::{role::RoleIndex, LocalType, MessageType};

        // Create a role with wildcard index: Worker[*]
        let worker = Role::with_index(format_ident!("Worker"), RoleIndex::Wildcard).unwrap();
        let msg = MessageType {
            name: format_ident!("Result"),
            type_annotation: None,
            payload: None,
        };
        let local_type = LocalType::Receive {
            from: worker,
            message: msg,
            continuation: Box::new(LocalType::End),
        };

        let tokens = generate_runner_body(&local_type, &mut RecursionContext::new());
        let output = tokens.to_string();

        // Check that we generate resolve_family and collect calls
        assert!(
            output.contains("resolve_family"),
            "Should use resolve_family for wildcard"
        );
        assert!(
            output.contains("collect"),
            "Should use collect for wildcard receive"
        );
    }

    #[test]
    fn test_generate_range_exprs_concrete() {
        use crate::ast::role::{RangeExpr, RoleRange};

        let range = RoleRange {
            start: RangeExpr::Concrete(1),
            end: RangeExpr::Concrete(5),
        };

        let (start, end) = generate_range_exprs(&range);
        assert_eq!(start.to_string(), "1u32");
        assert_eq!(end.to_string(), "5u32");
    }

    #[test]
    fn test_generate_range_exprs_symbolic() {
        use crate::ast::role::{RangeExpr, RoleRange};

        let range = RoleRange {
            start: RangeExpr::Symbolic("start".to_string()),
            end: RangeExpr::Symbolic("end".to_string()),
        };

        let (start, end) = generate_range_exprs(&range);
        assert_eq!(start.to_string(), "start");
        assert_eq!(end.to_string(), "end");
    }
