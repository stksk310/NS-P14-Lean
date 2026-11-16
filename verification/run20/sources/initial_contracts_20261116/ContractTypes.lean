module
import audit.run20.RequestedGoals
import NSP14.Ordinary.Closure
import NSP14.Width.Closure
import NSP14.Homological.ActualCoefficientBaseChange
import Lean
open Lean
set_option maxRecDepth 4096
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let names : Array Name := #[`NSP14.Run20.Requested.I_PARTITION,`NSP14.Run20.Requested.I_MAIN]
 for n in names do
  let ci ← getConstInfo n
  let ty ← Meta.ppExpr ci.type
  let ety ← withOptions (fun o => o.setBool `pp.explicit true) (Meta.ppExpr ci.type)
  let expanded ← Meta.forallTelescopeReducing (mkConst n) fun xs body => do
   let body ← Meta.whnf body
   let full ← Meta.mkForallFVars xs body
   return (← Meta.ppExpr full).pretty
  let axs ← collectAxioms n
  IO.println ((Json.mkObj [("name",toJson n.toString),("type",toJson ty.pretty),
    ("explicit_type",toJson ety.pretty),("expanded_type",toJson expanded),
    ("axioms",toJson (axs.map Name.toString))]).compress)
