module
import NSP14
import tests.Run14Fixtures
import tests.ActualSidon
import tests.OffsetStabilization
import tests.Run14Acceptance
import Lean
open Lean
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let included : Array String := #["tests.Run14Fixtures","tests.ActualSidon","tests.OffsetStabilization","tests.Run14Acceptance"]
 for (n,ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if modName == "NSP14" || modName.startsWith "NSP14." || included.contains modName then
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
   let type ← Lean.Meta.ppExpr ci.type
   let explicitType ← withOptions (fun opts => opts.setBool `pp.explicit true) (Lean.Meta.ppExpr ci.type)
   IO.println ((Json.mkObj [("name",toJson n.toString),("module",toJson modName),
    ("kind",toJson kind),("axioms",toJson (axs.map Name.toString)),
    ("type",toJson type.pretty),("explicit_type",toJson explicitType.pretty)]).compress)
