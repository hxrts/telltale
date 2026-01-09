import RumpsteakV2.Protocol.LocalTypeR
import RumpsteakV2.Protocol.LocalTypeDB
import RumpsteakV2.Protocol.CoTypes.EQ2

/-! # RumpsteakV2.Protocol.CoTypes.DBBridge

Bridge lemmas justified by the de Bruijn development. These are currently
axiomatized to unblock the EQ2 substitution pipeline; the intent is to
replace them with proofs once the DB commutation lemmas are established.
-/

namespace RumpsteakV2.Protocol.CoTypes

open RumpsteakV2.Protocol.LocalTypeR
open RumpsteakV2.Protocol.CoTypes.EQ2

axiom EQ2_subst_mu_comm_via_DB (body : LocalTypeR) (var t : String) (repl : LocalTypeR)
    (htne : t ≠ var) :
    EQ2 ((body.substitute var repl).substitute t (.mu t (body.substitute var repl)))
        ((body.substitute t (.mu t body)).substitute var repl)

end RumpsteakV2.Protocol.CoTypes
