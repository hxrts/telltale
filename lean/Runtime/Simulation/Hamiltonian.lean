import Runtime.Simulation.Core

set_option autoImplicit false

namespace Runtime.Simulation

structure HamiltonianParams where
  springConstant : Scalar
  mass : Scalar
  stepSize : Scalar

/-- Harmonic force used by the Rust Hamiltonian handler. -/
def hamiltonianForce (params : HamiltonianParams) (myPosition peerPosition : Scalar) : Scalar :=
  -params.springConstant * (myPosition - peerPosition)

/-- One Hamiltonian step for a role with phase-gated leapfrog integration. -/
def hamiltonianStep
    (params : HamiltonianParams)
    (phase : Nat)
    (peerPosition : Scalar)
    (state : List Scalar) : Except String (List Scalar) := do
  match state with
  | [position, momentum] =>
      if phase % 4 != 3 then
        pure [position, momentum]
      else
        let dt := params.stepSize
        let force := hamiltonianForce params position peerPosition
        let halfKick := momentum + force * dt / 2
        let driftPosition := position + halfKick / params.mass * dt
        let newForce := hamiltonianForce params driftPosition peerPosition
        let finalMomentum := halfKick + newForce * dt / 2
        pure [driftPosition, finalMomentum]
  | _ =>
      throw "Hamiltonian expects [position, momentum]"

end Runtime.Simulation
