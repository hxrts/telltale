import Distributed.Model.Assumptions
import Distributed.Model.ConsensusEnvelope
import Distributed.Families.FLP
import Distributed.Families.CAP
import Distributed.Families.QuorumGeometry
import Distributed.Families.PartialSynchrony
import Distributed.Families.Responsiveness
import Distributed.Families.Nakamoto
import Distributed.Families.Reconfiguration
import Distributed.Families.AtomicBroadcast
import Distributed.Families.AccountableSafety
import Distributed.Families.FailureDetectors
import Distributed.Families.DataAvailability
import Distributed.Families.Coordination
import Distributed.Families.CRDT
import Distributed.Transport.API

/-! # Distributed

Lean entry point for consensus assumption validation and theorem packaging.

This module provides a compact API for classifying protocol specifications
into BFT/Nakamoto/Hybrid spaces and validating built-in consensus assumptions.
-/
