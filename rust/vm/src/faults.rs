//! Stable fault taxonomy and machine-readable mapping helpers.

use crate::coroutine::Fault;
use serde::{Deserialize, Serialize};

/// Stable fault taxonomy used by snapshot tests and cross-target diagnostics.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum FaultClass {
    /// Session-type or value-shape mismatch.
    Type,
    /// Unknown branch/choice label.
    Label,
    /// Channel ownership/lifecycle violation.
    Channel,
    /// Signature/proof verification failure.
    Verification,
    /// Host effect invocation failure.
    Invoke,
    /// Guard/evidence acquisition failure.
    Acquire,
    /// Endpoint transfer/delegation failure.
    Transfer,
    /// Speculation/fork-join failure.
    Speculation,
    /// Session close lifecycle failure.
    Close,
    /// Information-flow policy violation.
    Flow,
    /// Progress-token discipline failure.
    Progress,
    /// Output-condition gating rejection.
    OutputCondition,
    /// Register-addressing failure.
    Register,
    /// Program-counter addressing failure.
    ProgramCounter,
    /// Buffer saturation/backpressure failure.
    Buffer,
    /// Deterministic credit budget exhaustion.
    Credits,
}

/// Classify a concrete runtime fault into the stable taxonomy.
#[must_use]
pub fn classify_fault(fault: &Fault) -> FaultClass {
    match fault {
        Fault::TypeViolation { .. } => FaultClass::Type,
        Fault::UnknownLabel { .. } => FaultClass::Label,
        Fault::ChannelClosed { .. } => FaultClass::Channel,
        Fault::InvalidSignature { .. } | Fault::VerificationFailed { .. } => {
            FaultClass::Verification
        }
        Fault::Invoke { .. } => FaultClass::Invoke,
        Fault::Acquire { .. } => FaultClass::Acquire,
        Fault::Transfer { .. } => FaultClass::Transfer,
        Fault::Speculation { .. } => FaultClass::Speculation,
        Fault::Close { .. } => FaultClass::Close,
        Fault::FlowViolation { .. } => FaultClass::Flow,
        Fault::NoProgressToken { .. } => FaultClass::Progress,
        Fault::OutputCondition { .. } => FaultClass::OutputCondition,
        Fault::OutOfRegisters => FaultClass::Register,
        Fault::PcOutOfBounds => FaultClass::ProgramCounter,
        Fault::BufferFull { .. } => FaultClass::Buffer,
        Fault::OutOfCredits => FaultClass::Credits,
    }
}

/// Stable machine-readable code for each fault class.
#[must_use]
pub fn fault_code(class: FaultClass) -> &'static str {
    match class {
        FaultClass::Type => "vm.fault.type",
        FaultClass::Label => "vm.fault.label",
        FaultClass::Channel => "vm.fault.channel",
        FaultClass::Verification => "vm.fault.verification",
        FaultClass::Invoke => "vm.fault.invoke",
        FaultClass::Acquire => "vm.fault.acquire",
        FaultClass::Transfer => "vm.fault.transfer",
        FaultClass::Speculation => "vm.fault.speculation",
        FaultClass::Close => "vm.fault.close",
        FaultClass::Flow => "vm.fault.flow",
        FaultClass::Progress => "vm.fault.progress",
        FaultClass::OutputCondition => "vm.fault.output_condition",
        FaultClass::Register => "vm.fault.register",
        FaultClass::ProgramCounter => "vm.fault.pc",
        FaultClass::Buffer => "vm.fault.buffer",
        FaultClass::Credits => "vm.fault.credits",
    }
}

/// Stable machine-readable code for a concrete runtime fault.
#[must_use]
pub fn fault_code_of(fault: &Fault) -> &'static str {
    fault_code(classify_fault(fault))
}

/// Build a stable transfer fault for a non-endpoint transfer source register.
#[must_use]
pub fn transfer_fault_expect_endpoint_register(role: &str) -> Fault {
    Fault::Transfer {
        message: format!("{role}: transfer expects endpoint register"),
    }
}

/// Build a stable transfer fault for a non-nat transfer target register.
#[must_use]
pub fn transfer_fault_expect_nat_target(role: &str) -> Fault {
    Fault::Transfer {
        message: format!("{role}: transfer expects nat target coroutine id"),
    }
}

/// Build a stable transfer fault when transfer target id is out of range.
#[must_use]
pub fn transfer_fault_target_id_out_of_range(role: &str) -> Fault {
    Fault::Transfer {
        message: format!("{role}: target id out of range"),
    }
}

/// Build a stable transfer fault when endpoint ownership is missing.
#[must_use]
pub fn transfer_fault_endpoint_not_owned() -> Fault {
    Fault::Transfer {
        message: "endpoint not owned".to_string(),
    }
}

/// Build a stable transfer fault for delegation-owner guard violations.
#[must_use]
pub fn transfer_fault_delegation_guard_violation(phase: &str) -> Fault {
    Fault::Transfer {
        message: format!("delegation guard violation {phase} transfer"),
    }
}

/// Build a stable speculation fault when speculation is disabled.
#[must_use]
pub fn speculation_fault_disabled() -> Fault {
    Fault::Speculation {
        message: "speculation disabled".to_string(),
    }
}

/// Build a stable speculation fault when join is attempted without active state.
#[must_use]
pub fn speculation_fault_join_requires_active() -> Fault {
    Fault::Speculation {
        message: "join requires active speculation".to_string(),
    }
}

/// Build a stable speculation fault when abort is attempted without active state.
#[must_use]
pub fn speculation_fault_abort_requires_active() -> Fault {
    Fault::Speculation {
        message: "abort requires active speculation".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instr::Endpoint;
    use crate::session::Edge;
    use telltale_types::ValType;

    #[test]
    fn fault_codes_are_stable_for_representative_variants() {
        let samples = [
            Fault::TypeViolation {
                expected: ValType::Unit,
                actual: ValType::Nat,
                message: "m".to_string(),
            },
            Fault::UnknownLabel {
                label: "x".to_string(),
            },
            Fault::ChannelClosed {
                endpoint: Endpoint {
                    sid: 1,
                    role: "A".to_string(),
                },
            },
            Fault::VerificationFailed {
                edge: Edge::new(1, "A", "B"),
                message: "bad sig".to_string(),
            },
            Fault::OutOfCredits,
        ];

        let codes: Vec<&str> = samples.iter().map(fault_code_of).collect();
        assert_eq!(
            codes,
            vec![
                "vm.fault.type",
                "vm.fault.label",
                "vm.fault.channel",
                "vm.fault.verification",
                "vm.fault.credits",
            ]
        );
    }
}
