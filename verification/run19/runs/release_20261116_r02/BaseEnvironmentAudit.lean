module
import NSP14
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let typed : Array String := #["NSP14.Endpoint.CarrySums","NSP14.Endpoint.CompetitorBounds","NSP14.Endpoint.FiniteCompetitors","NSP14.Endpoint.FiniteSocleBounds","NSP14.Width.AntipodalComparison","NSP14.Width.DenseComparison","NSP14.Width.DenseLexResources","NSP14.Width.DensePayment","NSP14.Width.FiveHigher","NSP14.Width.FiveNonAntipodal","NSP14.Width.SparseHigher"]
 IO.println ((Json.mkObj [("audit_metadata",toJson true),("imported_modules",toJson (env.header.moduleNames.map Name.toString))]).compress)
 for (n,ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if typed.contains modName then
   let axs ← collectAxioms n
   let kind := match ci with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "def"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
   let mut fields := [("name",toJson n.toString),("module",toJson modName),("kind",toJson kind),("axioms",toJson (axs.map Name.toString))]
   if typed.contains modName then
    let type ← Lean.Meta.ppExpr ci.type
    let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
    fields := fields ++ [("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]
   IO.println ((Json.mkObj fields).compress)
