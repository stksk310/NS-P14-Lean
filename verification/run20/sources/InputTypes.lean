module
import audit.run19.ClosedGoals
import NSP14.Ordinary.Closure
import NSP14.Width.Closure
import NSP14.Homological.ActualCoefficientBaseChange
import Lean
open Lean
set_option maxRecDepth 4096
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let names : Array Name := #[``NSP14.SmallEmbedding.base_comparison,``NSP14.SmallEmbedding.three_comparison,``NSP14.NarrowFour.narrow_four_comparison,``NSP14.NumericalSemigroup.narrow_width_comparison,``NSP14.Ordinary.ordinary_actual_completion_betti_le,``NSP14.NumericalSemigroup.intervalCompletionAll_carrier,``NSP14.NumericalSemigroup.intervalCompletionAll_carrier_eq,``NSP14.NumericalSemigroup.carrier_totalBetti,``NSP14.NumericalSemigroup.completed_totalBetti,``NSP14.NumericalSemigroup.actualG_totalBetti_baseChange,``NSP14.NumericalSemigroup.actualCutRank_two_le,``NSP14.NumericalSemigroup.actualCutRank_le,``NSP14.NumericalSemigroup.actualCutRank_triangular,``NSP14.NumericalSemigroup.degree_two_le_deficit,``NSP14.Run19.distance_closed,``NSP14.Run19.words_closed,``NSP14.Run19.high_closed,``NSP14.Run19.first_closed,``NSP14.Run19.small_closed,``NSP14.Run19.width4_closed,``NSP14.Run19.narrow_four_closed,``NSP14.Run19.base_closed,``NSP14.Run19.ltv_closed,``NSP14.Run19.three_closed]
 for n in names do
  let ci ← getConstInfo n
  let ty ← Meta.ppExpr ci.type
  let ety ← withOptions (fun o => o.setBool `pp.explicit true) (Meta.ppExpr ci.type)
  let expanded ← Meta.forallTelescopeReducing ci.type fun xs body => do
   let body ← Meta.whnf body
   let full ← Meta.mkForallFVars xs body
   return (← Meta.ppExpr full).pretty
  let axs ← collectAxioms n
  IO.println ((Json.mkObj [("name",toJson n.toString),("type",toJson ty.pretty),
    ("explicit_type",toJson ety.pretty),("expanded_type",toJson expanded),
    ("axioms",toJson (axs.map Name.toString))]).compress)
