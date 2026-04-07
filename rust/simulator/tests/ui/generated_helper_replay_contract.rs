use telltale_machine::ProtocolMachineSemanticObjects;
use telltale_simulator::generated::{GeneratedEffectScenario, GeneratedEffectSimulationReport};

fn main() {
    let report = GeneratedEffectSimulationReport::new(
        GeneratedEffectScenario::default(),
        ProtocolMachineSemanticObjects::default(),
        Vec::new(),
    );
    let _ = report.replay;
}
