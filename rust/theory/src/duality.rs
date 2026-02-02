//! Duality for Session Types
//!
//! This module computes dual types for binary session type communication.
//! The dual of a type represents the "other side" of a communication channel.
//!
//! # Duality Rules
//!
//! - `dual(end) = end`
//! - `dual(!p{lᵢ.Tᵢ}) = ?p{lᵢ.dual(Tᵢ)}`
//! - `dual(?p{lᵢ.Tᵢ}) = !p{lᵢ.dual(Tᵢ)}`
//! - `dual(μt.T) = μt.dual(T)`
//! - `dual(t) = t`

use telltale_types::LocalTypeR;

/// Compute the dual of a local type.
///
/// The dual swaps all send and receive operations while preserving
/// the structure and partners.
///
/// # Examples
///
/// ```
/// use telltale_theory::dual;
/// use telltale_types::{LocalTypeR, Label};
///
/// let send = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// let recv = dual(&send);
///
/// assert!(matches!(recv, LocalTypeR::Recv { partner, .. } if partner == "B"));
/// ```
pub fn dual(lt: &LocalTypeR) -> LocalTypeR {
    lt.dual()
}

/// Check if two local types are duals of each other.
///
/// Two types are duals if one is the dual of the other.
///
/// # Examples
///
/// ```
/// use telltale_theory::{dual, is_dual};
/// use telltale_types::{LocalTypeR, Label};
///
/// let send = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
/// let recv = LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::End);
///
/// assert!(is_dual(&send, &recv));
/// ```
pub fn is_dual(t1: &LocalTypeR, t2: &LocalTypeR) -> bool {
    &t1.dual() == t2
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_matches::assert_matches;
    use telltale_types::Label;

    #[test]
    fn test_dual_end() {
        assert_eq!(dual(&LocalTypeR::End), LocalTypeR::End);
    }

    #[test]
    fn test_dual_send() {
        let send = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let recv = dual(&send);

        assert_matches!(recv, LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "B");
            assert_eq!(branches.len(), 1);
            assert_eq!(branches[0].0.name, "msg");
            assert_eq!(branches[0].2, LocalTypeR::End);
        });
    }

    #[test]
    fn test_dual_recv() {
        let recv = LocalTypeR::recv("A", Label::new("data"), LocalTypeR::End);
        let send = dual(&recv);

        assert_matches!(send, LocalTypeR::Send { partner, branches } => {
            assert_eq!(partner, "A");
            assert_eq!(branches.len(), 1);
        });
    }

    #[test]
    fn test_dual_recursive() {
        let t = LocalTypeR::mu(
            "loop",
            LocalTypeR::send("B", Label::new("ping"), LocalTypeR::var("loop")),
        );
        let d = dual(&t);

        assert_matches!(d, LocalTypeR::Mu { var, body } => {
            assert_eq!(var, "loop");
            assert_matches!(body.as_ref(), LocalTypeR::Recv { .. });
        });
    }

    #[test]
    fn test_dual_involution() {
        // dual(dual(T)) = T
        let t = LocalTypeR::send(
            "B",
            Label::new("x"),
            LocalTypeR::recv("B", Label::new("y"), LocalTypeR::End),
        );

        assert_eq!(dual(&dual(&t)), t);
    }

    #[test]
    fn test_is_dual() {
        let send = LocalTypeR::send("B", Label::new("msg"), LocalTypeR::End);
        let recv = LocalTypeR::recv("B", Label::new("msg"), LocalTypeR::End);

        assert!(is_dual(&send, &recv));
        assert!(is_dual(&recv, &send));
        assert!(!is_dual(&send, &send));
    }

    #[test]
    fn test_dual_choice() {
        let t = LocalTypeR::send_choice(
            "B",
            vec![
                (Label::new("yes"), None, LocalTypeR::End),
                (Label::new("no"), None, LocalTypeR::End),
            ],
        );
        let d = dual(&t);

        assert_matches!(d, LocalTypeR::Recv { partner, branches } => {
            assert_eq!(partner, "B");
            assert_eq!(branches.len(), 2);
        });
    }
}
