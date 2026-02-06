import Runtime.ProgramLogic.WPPair
import Runtime.Compat.RA

/- 
The Problem. Composed WP rules like send pipelines currently duplicate the
same open/interact/close reasoning found in each instruction rule.

Solution Structure. Express composed WPs as chains of `wp_pair` instances,
leaving the algebraic proof structure to future refinement.
-/

set_option autoImplicit false
noncomputable section

universe u

variable [Telltale.TelltaleIris]
variable {γ ε : Type u} [GuardLayer γ] [EffectModel ε]

def wp_send_pipeline (layer : γ) (action : EffectModel.EffectAction ε) : iProp :=
  -- Placeholder: acquire + invoke + send via chained wp_pair rules.
  iProp.sep
    (wp_pair (acquirePair (γ:=γ) (ε:=ε) layer))
    (iProp.sep
      (wp_pair (invokePair (γ:=γ) (ε:=ε) action))
      (wp_pair (sendPair (γ:=γ) (ε:=ε))))
