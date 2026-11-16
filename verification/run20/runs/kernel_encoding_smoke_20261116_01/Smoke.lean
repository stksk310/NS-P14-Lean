module
import all NSP14.Main
import Lean
open Lean
namespace Run20TypeEncoding
partial def canonical : Lean.Expr → Lean.Expr
 | .forallE _ d b bi => .forallE `_ (canonical d) (canonical b) bi
 | .lam _ d b bi => .lam `_ (canonical d) (canonical b) bi
 | .letE _ t v b nd => .letE `_ (canonical t) (canonical v) (canonical b) nd
 | .app f a => .app (canonical f) (canonical a)
 | .proj n i e => .proj n i (canonical e)
 | .mdata _ e => canonical e
 | e => e
end Run20TypeEncoding
set_option maxRecDepth 4000
set_option maxHeartbeats 0
#eval show MetaM Unit from do
 let env ← getEnv
 let typed : Array String := #["NSP14.Main"]
 let typedSet := Std.HashSet.ofArray typed
 IO.println ((Json.mkObj [("audit_metadata",toJson true),("imported_modules",toJson (env.header.moduleNames.map Name.toString))]).compress)
 let mut inventory : Array String := #[]
 for (n,_) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if typedSet.contains modName then inventory := inventory.push n.toString
 IO.println ((Json.mkObj [("declaration_inventory",toJson inventory)]).compress)
 for (n,ci) in env.constants.toList do
  let some idx := env.getModuleIdxFor? n | continue
  let modName := env.header.moduleNames[idx.toNat]!.toString
  if typedSet.contains modName then
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
   if typedSet.contains modName then
    let type ← Lean.Meta.ppExpr ci.type
    let canonicalType := Run20TypeEncoding.canonical ci.type
    unless canonicalType == ci.type do throwError "kernel type alpha roundtrip failed: {n}"
    let explicitType := canonicalType.toString
    fields := fields ++ [("type",toJson type.pretty),("explicit_type",toJson explicitType),("kernel_type",toJson ci.type.toString),("kernel_alpha_roundtrip",toJson true),("universe_parameters",toJson (ci.levelParams.map Name.toString))]
   if #["NSP14.NumericalSemigroup.p14_totalBetti_le_intervalCompletion","NSP14.Run20.partition_closed","NSP14.Run20.main_closed"].contains n.toString then
    let pretty ← withOptions (fun o => o.setBool `pp.all true |>.setBool `pp.tagAppFns false) (Lean.Meta.ppExpr ci.type)
    fields := fields ++ [("pretty_explicit_type",toJson pretty.pretty)]
   IO.println ((Json.mkObj fields).compress)
