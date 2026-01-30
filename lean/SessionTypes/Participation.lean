import SessionTypes.Participation.Core
import SessionTypes.Participation.Extra

/-! # SessionTypes.Participation

Participation predicates for projection proofs.

These predicates classify whether a role is a "participant" in a global protocol
(appears on a communication path) or a "non-participant" (not involved in any
communication). This classification is crucial for projection soundness proofs.

## Expose

The following definitions form the semantic interface for proofs:

- `part_of2`: role participates in the protocol (exists path to communication)
- `part_of_all2`: role participates on all branches (for coherence proofs)
- `part_of2_or_not`: classification lemma (participant or not)
- `comp_dir`: direction of participation (sender, receiver, or none)
-/
