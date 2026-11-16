module
import Lean
open Lean
namespace Run20TypeEncoding
partial def canonical (depth : Nat) : Lean.Expr → Lean.Expr
 | .forallE _ d b bi => .forallE (.str .anonymous ("__run20_binder_"++toString depth)) (canonical depth d) (canonical (depth+1) b) bi
 | .lam _ d b bi => .lam (.str .anonymous ("__run20_binder_"++toString depth)) (canonical depth d) (canonical (depth+1) b) bi
 | .letE _ t v b nd => .letE (.str .anonymous ("__run20_binder_"++toString depth)) (canonical depth t) (canonical depth v) (canonical (depth+1) b) nd
 | .app f a => .app (canonical depth f) (canonical depth a)
 | .proj n i e => .proj n i (canonical depth e)
 | .mdata d e => .mdata d (canonical depth e)
 | e => e
end Run20TypeEncoding
set_option maxHeartbeats 0
set_option maxRecDepth 4000
#eval show MetaM Unit from do
 let nat := mkConst ``Nat
 let eqxy := mkApp3 (mkConst ``Eq [Level.zero]) nat (mkBVar 1) (mkBVar 0)
 let eqyx := mkApp3 (mkConst ``Eq [Level.zero]) nat (mkBVar 0) (mkBVar 1)
 let mk (a b : Name) (body : Expr) := mkForall a .default nat (mkForall b .default nat body)
 let first := mk `x `y eqxy
 let renamed := mk `other `last eqxy
 let swapped := mk `x `y eqyx
 let norm (e : Expr) := Run20TypeEncoding.canonical 0 e
 unless norm first == first do throwError "alpha equivalence lost"
 unless (toString (norm first)) == toString (norm renamed) do throwError "alpha names not canonical"
 if (toString (norm first)) == toString (norm swapped) then throwError "bound-variable indices collapsed"
 let explicit := mkForall `x .default nat (mkBVar 0)
 let implicit := mkForall `x .implicit nat (mkBVar 0)
 let instanceBinder := mkForall `x .instImplicit nat (mkBVar 0)
 if (toString (norm explicit)) == toString (norm implicit) then throwError "implicit binder collapsed"
 if (toString (norm implicit)) == toString (norm instanceBinder) then throwError "instance binder collapsed"
 if toString (norm (.sort Level.zero)) == toString (norm (.sort (.succ Level.zero))) then throwError "universes collapsed"
 unless norm (.mdata {} first) == .mdata {} first do throwError "metadata was not preserved"
 let mut deep := mkNatLit 0
 for _ in [:200] do deep := mkApp (mkConst ``Nat.succ) deep
 let raw := toString (norm deep)
 unless (raw.splitOn "Nat.succ").length==201 do throwError "deep kernel term was elided"
 if raw.contains '⋯' || raw.contains '…' then throwError "kernel display omission"
 let controls := #["actual alpha-equivalence", "binder renaming", "bound-variable order",
   "explicit/implicit binder", "instance binder", "universe levels", "exact metadata preservation",
   "all 200 nested applications", "no display ellipses"]
 IO.println ((Json.mkObj [("status",toJson "PASS_COMPLETE_KERNEL_TYPE_ENCODING"),("controls",toJson controls)]).compress)
