//! Selected-operation compiler obligations: refusal is not executable transfer.

use std::collections::BTreeMap;
use std::num::NonZeroU64;

use telltale::{compile_operation_image, CommandCompileError};

const HEADER: &str = r#"
effect Runtime
  authoritative ready : Session -> Result ReadyError ReadyWitness
  {
    class : authoritative
    progress : may_block
    region : fragment
    agreement_use : required
    reentrancy : reject_same_fragment
  }
type ReadyError =
  | NotReady
type alias ReadyWitness =
{
  epoch : Int
}
agreement_profile Selected
  visibility immediate
  rule no_agreement
  usable_at none
  finalized_at none
  evidence witness
operation Flow at A progress Progress within bounded agreement Selected =
"#;

fn source(body: &str) -> String {
    let text = format!("{HEADER}{body}\nprotocol Envelope uses Runtime =\n  roles A, B, C\n  A -> B : Start\n  B -> C : Forward\n");
    telltale_language::parse_choreography_str(&text)
        .expect("fixture parent parses before selected-body validation")
        .validate()
        .expect(
            "fixture parent genuinely uses every declared role before selected-body validation",
        );
    text
}

fn compile(
    body: &str,
) -> Result<telltale_machine::runtime::loader::CodeImage, CommandCompileError> {
    compile_operation_image(
        &source(body),
        "Flow",
        &BTreeMap::from([(
            "bounded".into(),
            NonZeroU64::new(64).expect("original logical budget"),
        )]),
    )
}

fn require_linear_refusal(body: &str, expected: &str) {
    let error = compile(body).expect_err("invalid original obligation cannot produce an image");
    let CommandCompileError::Parse(original) = error else {
        panic!("expected original linear source refusal before lowering, got {error}");
    };
    assert!(
        original.to_string().contains(expected),
        "original source diagnostic: {original}"
    );
}

fn require_unsupported_control(body: &str) {
    let text = source(body);
    let parent =
        telltale_language::parse_choreography_str(&text).expect("valid adjacent declaration");
    telltale_language::parse_declared_operation(&parent, "Flow")
        .expect("actual selected construct parses and validates; not a syntax-failure substitute");
    let error = compile(body).expect_err("unlowered operation must not yield an executable image");
    assert!(
        matches!(error, CommandCompileError::Unsupported(_)),
        "unexpected original refusal: {error}"
    );
}

#[test]
fn selected_operation_rejects_dropped_and_duplicated_original_receipts() {
    require_linear_refusal(
        "  let receipt = transfer Session from A to B\n  A -> B : Notice",
        "linear binding 'receipt' is never consumed",
    );
    require_linear_refusal(
        "  let receipt = transfer Session from A to B\n  A -> B : First(receipt)\n  A -> C : Second(receipt)",
        "linear binding 'receipt' is consumed more than once",
    );
    require_unsupported_control(
        "  let receipt = transfer Session from A to B\n  handoff Flow to B with receipt",
    );
}

#[test]
fn selected_operation_rejects_receipt_divergence_across_choice_and_result() {
    require_linear_refusal(
        "  let receipt = transfer Session from A to B\n  choice A at\n    | Commit =>\n        handoff Flow to B with receipt\n    | Abort =>\n        A -> B : Abort",
        "linear binding 'receipt' diverges across choice branches",
    );
    require_linear_refusal(
        "  let receipt = transfer Session from A to B\n  authoritative let readiness = check Runtime.ready(session)\n  case readiness of\n    | Ok(witness) =>\n        handoff Flow to B with receipt\n    | Err(reason) =>\n        A -> B : Abort(reason)",
        "linear binding 'receipt' diverges across choice branches",
    );
    require_unsupported_control(
        "  begin Flow\n  choice A at\n    | Commit =>\n        A -> B : Commit\n    | Abort =>\n        A -> B : Abort",
    );
}

#[test]
fn selected_operation_rejects_distinct_timeout_and_cancel_receipt_divergence() {
    require_linear_refusal(
        "  let receipt = transfer Session from A to B\n  timeout 5s A at\n    A -> B : Ready\n  on timeout =>\n    handoff Flow to B with receipt\n  on cancel =>\n    A -> B : Cancelled",
        "timeout branches must preserve linear assets",
    );
    require_linear_refusal(
        "  let receipt = transfer Session from A to B\n  timeout 5s A at\n    A -> B : Ready\n  on timeout =>\n    A -> B : Retry\n  on cancel =>\n    handoff Flow to B with receipt",
        "cancel branches must preserve linear assets",
    );
    require_unsupported_control(
        "  begin Flow\n  timeout 5s A at\n    A -> B : Ready\n  on timeout =>\n    A -> B : Retry\n  on cancel =>\n    A -> B : Cancelled",
    );
}

#[test]
fn selected_operation_rejects_receipt_loss_across_recursion_and_parallel_arms() {
    require_linear_refusal(
        "  let receipt = transfer Session from A to B\n  rec Retry\n    handoff Flow to B with receipt\n    continue Retry",
        "recursive body must preserve linear assets across unfoldings",
    );
    require_linear_refusal(
        "  let receipt = transfer Session from A to B\n  par\n    | handoff Flow to B with receipt\n    | A -> C : Audit",
        "parallel branches must preserve linear assets",
    );
    require_unsupported_control("  begin Flow\n  rec Retry\n    A -> B : Tick\n    continue Retry");
    require_unsupported_control("  begin Flow\n  par\n    | A -> B : Seen\n    | A -> C : Audit");
}

#[test]
fn selected_empty_original_operation_remains_a_valid_owned_loader_control() {
    let image = compile("  begin Flow\n  await Flow\n  resolve Flow as Success")
        .expect("supported adjacent original transaction");
    let mut machine = telltale_machine::ProtocolMachine::new(Default::default());
    let _owner = machine
        .load_choreography_owned(&image, "original/control")
        .expect("actual supported image owning admission");
    assert!(
        machine.operation_instances().is_empty(),
        "loader must not execute Begin"
    );
    assert!(
        machine.effect_trace().is_empty(),
        "no host callback was invoked by compilation/admission"
    );
}
