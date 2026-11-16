module
import NSP14.Ordinary.Scalarization
import Lean
open Lean
-- NEGATIVE CONTROL ONLY. This file is never imported by production, fixtures or the main environment audit.
-- The declaration below must be rejected; it is not a dependency of any project proof.
axiom Run18AxiomPolicyProbe.extra : True
#eval show MetaM Unit from do
 for n in [``NSP14.Ordinary.Scalarization.weight_head_le, ``Run18AxiomPolicyProbe.extra] do
  let ci ← getConstInfo n
  let kind := match ci with
   | .axiomInfo _ => "axiom"
   | .thmInfo _ => "theorem"
   | _ => "other"
  let axs ← collectAxioms n
  IO.println ((Json.mkObj [("name",toJson n.toString),("kind",toJson kind),
   ("axioms",toJson (axs.map Name.toString))]).compress)
