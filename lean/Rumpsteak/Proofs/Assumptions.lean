/-! # Rumpsteak.Proofs.Assumptions

Axioms and trust assumptions for the verification system.

## Overview

This module centralizes any axiomatic assumptions required by the proofs.
Currently, the Rumpsteak verification aims to prove all properties constructively
from the definitions, following the literature.

## Current Status

No axioms are currently required. The safety theorems (Subject Reduction, Progress)
are being proven constructively following the methodology in:
- "A Very Gentle Introduction to Multiparty Session Types" (Yoshida & Gheri)
- "Precise Subtyping for Asynchronous Multiparty Sessions" (Ghilezan et al., POPL 2021)

## Review Notes

Reviewers should audit this file carefully. Any axioms added here represent
trust assumptions in the verification system.
-/

namespace Rumpsteak.Proofs.Assumptions

-- No axioms currently required.
-- All verification properties are being proven constructively from the definitions.

end Rumpsteak.Proofs.Assumptions
