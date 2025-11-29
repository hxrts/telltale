-- Simple sanity checks to guard runner diagnostics.
import Rumpsteak.Subtyping
import Rumpsteak.Projection

open Rumpsteak.Projection
open Rumpsteak.Subtyping

namespace Rumpsteak.Diagnostics

/-- Construct two local actions for quick boolean checks. -/
private def sendA : LocalAction := { kind := LocalKind.send, partner := "P", label := "A" }
private def sendB : LocalAction := { kind := LocalKind.send, partner := "P", label := "B" }

private def ltShort : LocalType := { actions := [sendA] }
private def ltLong  : LocalType := { actions := [sendA, sendB] }

/-- A longer trace cannot be a subtype of a shorter one; guards the subsequence check. -/
example : isSubtype ltLong ltShort = false := by decide

/-- A trace with an unseen label fails the label subset check. -/
private def recvC : LocalAction := { kind := LocalKind.recv, partner := "P", label := "C" }
private def ltExtra : LocalType := { actions := [sendA, recvC] }
example : Rumpsteak.Projection.subLabelsOf ltExtra ltShort = false := by decide

end Rumpsteak.Diagnostics
