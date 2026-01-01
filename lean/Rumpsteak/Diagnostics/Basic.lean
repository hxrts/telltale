import Rumpsteak.Protocol.Core
import Rumpsteak.Protocol.Projection
import Rumpsteak.Protocol.Subtyping

/-! # Rumpsteak.Diagnostics.Basic

Basic sanity checks for the verification system.

## Overview

This module contains compile-time sanity checks that verify the subtyping
and label-subset predicates behave correctly on simple test cases.
These examples guard against regressions in the core validation logic.

## Main Results

- Example showing a longer trace is not a subtype of a shorter one
- Example showing traces with unseen labels fail the subset check
-/

namespace Rumpsteak.Diagnostics.Basic

open Rumpsteak.Protocol.Core
open Rumpsteak.Protocol.Projection
open Rumpsteak.Protocol.Subtyping

/-! ## Test Fixtures -/

/-- A send action to partner P with label A. -/
private def sendA : LocalAction := { kind := LocalKind.send, partner := "P", label := "A" }

/-- A send action to partner P with label B. -/
private def sendB : LocalAction := { kind := LocalKind.send, partner := "P", label := "B" }

/-- A receive action from partner P with label C. -/
private def recvC : LocalAction := { kind := LocalKind.recv, partner := "P", label := "C" }

/-- A local type with just sendA. -/
private def ltShort : LocalType := { actions := [sendA] }

/-- A local type with sendA followed by sendB. -/
private def ltLong : LocalType := { actions := [sendA, sendB] }

/-- A local type with sendA and recvC. -/
private def ltExtra : LocalType := { actions := [sendA, recvC] }

/-! ## Sanity Checks -/

/-- A longer trace cannot be a subtype of a shorter one.
    This guards the subsequence/length check in isSubtype. -/
example : isSubtype ltLong ltShort = false := by native_decide

/-- A trace with an unseen label fails the label subset check.
    This guards the subLabelsOf predicate. -/
example : subLabelsOf ltExtra ltShort = false := by native_decide

/-- Self-subtyping always succeeds. -/
example : isSubtype ltShort ltShort = true := by native_decide

/-- Self-sublabels always succeeds. -/
example : subLabelsOf ltShort ltShort = true := by native_decide

end Rumpsteak.Diagnostics.Basic
