module
import audit.run19.RequestedGoals
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 for n in #[`NSP14.Run19.Requested.N_DISTANCE,`NSP14.Run19.Requested.N_WORDS,
   `NSP14.Run19.Requested.N_HIGH,`NSP14.Run19.Requested.N_FIRST,`NSP14.Run19.Requested.N_SMALL,
   `NSP14.Run19.Requested.N_WIDTH4,`NSP14.Run19.Requested.N_CLOSE,`NSP14.Run19.Requested.I_BASE,
   `NSP14.Run19.Requested.X_LTV,`NSP14.Run19.Requested.I_THREE] do
  let ci ← getConstInfo n
  let some value := ci.value? | throwError "contract body unavailable: {n}"
  let body ← Lean.Meta.ppExpr value
  let explicitBody ← withOptions (fun o => o.setBool `pp.explicit true) (Lean.Meta.ppExpr value)
  let ax ← collectAxioms n
  IO.println ((Json.mkObj [("name",toJson n.toString),("type",toJson "Prop"),
    ("body",toJson body.pretty),("explicit_body",toJson explicitBody.pretty),
    ("axioms",toJson (ax.map Name.toString))]).compress)
