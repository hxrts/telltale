import Runtime.Proofs.Examples.EnvelopeEvidence

/-! # Theorem Evidence Export

Prints the theorem-pack evidence inventory of
`Runtime.Proofs.Examples.envelopeEvidencePack` as a JSON object
`{key: bool}` for Rust `LeanEvidenceInventory::from_json_str`. The printed
list is `envelopeEvidenceInventory`, proved equal to the pack's
`theoremInventory` by `envelopeEvidenceInventory_eq`. -/

set_option autoImplicit false

def main : IO Unit :=
  IO.println (Runtime.Proofs.inventoryToJson
    Runtime.Proofs.Examples.envelopeEvidenceInventory).compress
