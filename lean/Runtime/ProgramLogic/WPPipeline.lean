import Runtime.ProgramLogic.WPPair
import IrisExtractionInstance

/- 
The Problem. Composed WP rules like send pipelines currently duplicate the
same open/interact/close reasoning found in each instruction rule.

Solution Structure. Express composed WPs as chains of `wp_pair` instances in a
schematic layer, leaving the algebraic proof structure to future refinement.
-/

set_option autoImplicit false
section

universe u

variable [Telltale.TelltaleIris]
variable {γ ε : Type u} [GuardLayer γ] [EffectRuntime ε]

def wp_send_pipeline_schematic (layer : γ) (action : EffectRuntime.EffectAction ε) : iProp :=
  -- Schematic pipeline: acquire + invoke + send via chained wp_pair rules.
  iProp.sep
    (wp_pair (acquirePair (γ:=γ) (ε:=ε) layer))
    (iProp.sep
      (wp_pair (invokePair (γ:=γ) (ε:=ε) action))
      (wp_pair (sendPair (γ:=γ) (ε:=ε))))

abbrev wp_send_pipeline (layer : γ) (action : EffectRuntime.EffectAction ε) : iProp :=
  wp_send_pipeline_schematic (γ:=γ) (ε:=ε) layer action
