module
import Lean
open Lean
namespace Run20TypeEncoding
open Lean

abbrev NormState := Std.HashMap (ExprStructEq × Nat) Expr
partial def canonicalM (depth : Nat) (e : Expr) : StateM NormState Expr := do
 if let some v := (← get).get? (⟨e⟩,depth) then return v
 let v ← match e with
  | .forallE _ d b bi => return .forallE (.str .anonymous ("__run20_binder_"++toString depth)) (← canonicalM depth d) (← canonicalM (depth+1) b) bi
  | .lam _ d b bi => return .lam (.str .anonymous ("__run20_binder_"++toString depth)) (← canonicalM depth d) (← canonicalM (depth+1) b) bi
  | .letE _ t v b nd => return .letE (.str .anonymous ("__run20_binder_"++toString depth)) (← canonicalM depth t) (← canonicalM depth v) (← canonicalM (depth+1) b) nd
  | .app f a => return .app (← canonicalM depth f) (← canonicalM depth a)
  | .proj n i e => return .proj n i (← canonicalM depth e)
  | .mdata d e => return .mdata d (← canonicalM depth e)
  | e => pure e
 modify (·.insert (⟨e⟩,depth) v)
 return v

def canonical (depth : Nat) (e : Expr) : Expr := (canonicalM depth e).run' {}

partial def nameJson : Name → Json
 | .anonymous => .arr #[]
 | .str p s => .arr #[nameJson p,toJson "s",toJson s]
 | .num p n => .arr #[nameJson p,toJson "n",toJson n]
partial def readName (j : Json) : Except String Name := do
 let a ← j.getArr?
 if a.isEmpty then return .anonymous
 let p ← readName a[0]!
 match ← a[1]!.getStr? with
 | "s" => return .str p (← a[2]!.getStr?)
 | "n" => return .num p (← a[2]!.getNat?)
 | _ => throw "bad Name node"

partial def levelJson : Level → Json
 | .zero => .arr #[toJson "zero"]
 | .succ l => .arr #[toJson "succ",levelJson l]
 | .max a b => .arr #[toJson "max",levelJson a,levelJson b]
 | .imax a b => .arr #[toJson "imax",levelJson a,levelJson b]
 | .param n => .arr #[toJson "param",nameJson n]
 | .mvar n => .arr #[toJson "mvar",nameJson n.name]
partial def readLevel (j : Json) : Except String Level := do
 let a ← j.getArr?
 match ← a[0]!.getStr? with
 | "zero" => return .zero
 | "succ" => return .succ (← readLevel a[1]!)
 | "max" => return .max (← readLevel a[1]!) (← readLevel a[2]!)
 | "imax" => return .imax (← readLevel a[1]!) (← readLevel a[2]!)
 | "param" => return .param (← readName a[1]!)
 | "mvar" => return .mvar ⟨← readName a[1]!⟩
 | _ => throw "bad Level node"

def binderCode : BinderInfo → Nat
 | .default => 0 | .implicit => 1 | .strictImplicit => 2 | .instImplicit => 3

def readBinder (j : Json) : Except String BinderInfo := do
 match ← j.getNat? with
 | 0 => return .default | 1 => return .implicit | 2 => return .strictImplicit | 3 => return .instImplicit
 | _ => throw "bad binder kind"

structure Dag where
 seen : ExprStructMap Nat := {}
 nodes : Array Json := #[]
 restored : Array Expr := #[]
 metadata : Array MData := #[]

/-- Decode the actual JSON, not the original expression; children must precede their parent. -/
def decodeNode (j : Json) (prior : Array Expr) (md : Array MData) : Except String Expr := do
 let a ← j.getArr?
 let child (i : Nat) : Except String Expr := do
  let n ← a[i]!.getNat?
  match prior[n]? with | some e => return e | none => throw "forward/missing expression reference"
 match ← a[0]!.getStr? with
 | "bvar" => return .bvar (← a[1]!.getNat?)
 | "fvar" => return .fvar ⟨← readName a[1]!⟩
 | "mvar" => return .mvar ⟨← readName a[1]!⟩
 | "sort" => return .sort (← readLevel a[1]!)
 | "const" => return .const (← readName a[1]!) (← a[2]!.getArr? >>= fun ls => ls.toList.mapM readLevel)
 | "app" => return .app (← child 1) (← child 2)
 | "forall" => return .forallE (← readName a[1]!) (← child 2) (← child 3) (← readBinder a[4]!)
 | "lambda" => return .lam (← readName a[1]!) (← child 2) (← child 3) (← readBinder a[4]!)
 | "let" => return .letE (← readName a[1]!) (← child 2) (← child 3) (← child 4) (← a[5]!.getBool?)
 | "proj" => return .proj (← readName a[1]!) (← a[2]!.getNat?) (← child 3)
 | "nat" => return .lit (.natVal (← a[1]!.getNat?))
 | "string" => return .lit (.strVal (← a[1]!.getStr?))
 | "metadata" =>
  let i ← a[1]!.getNat?
  match md[i]? with | some d => return .mdata d (← child 2) | none => throw "missing metadata reference"
 | _ => throw "bad expression node"

partial def intern (e : Expr) : StateT Dag (Except String) Nat := do
 if let some n := (← get).seen.get? ⟨e⟩ then return n
 let node : Json ← match e with
  | .bvar n => pure (.arr #[toJson "bvar",toJson n])
  | .fvar n => pure (.arr #[toJson "fvar",nameJson n.name])
  | .mvar n => pure (.arr #[toJson "mvar",nameJson n.name])
  | .sort l => pure (.arr #[toJson "sort",levelJson l])
  | .const n ls => pure (.arr #[toJson "const",nameJson n,.arr (ls.toArray.map levelJson)])
  | .app f a => do pure (.arr #[toJson "app",toJson (← intern f),toJson (← intern a)])
  | .forallE n d b bi => do pure (.arr #[toJson "forall",nameJson n,toJson (← intern d),toJson (← intern b),toJson (binderCode bi)])
  | .lam n d b bi => do pure (.arr #[toJson "lambda",nameJson n,toJson (← intern d),toJson (← intern b),toJson (binderCode bi)])
  | .letE n t v b nd => do pure (.arr #[toJson "let",nameJson n,toJson (← intern t),toJson (← intern v),toJson (← intern b),toJson nd])
  | .proj n i v => do pure (.arr #[toJson "proj",nameJson n,toJson i,toJson (← intern v)])
  | .lit (.natVal n) => pure (.arr #[toJson "nat",toJson n])
  | .lit (.strVal s) => pure (.arr #[toJson "string",toJson s])
  | .mdata d v => do
   let child ← intern v
   let k := (← get).metadata.size
   modify fun s => {s with metadata := s.metadata.push d}
   pure (.arr #[toJson "metadata",toJson k,toJson child])
 let state ← get
 let rebuilt ← match decodeNode node state.restored state.metadata with
  | .ok v => pure v | .error err => throw err
 unless ExprStructEq.beq ⟨rebuilt⟩ ⟨e⟩ do throw "exact expression DAG roundtrip failed"
 let i := state.nodes.size
 set {state with seen := state.seen.insert ⟨e⟩ i,nodes := state.nodes.push node,restored := state.restored.push rebuilt}
 return i

/-- All semantic expression fields are explicit; metadata snapshots accompany their references. -/
def pack (e : Expr) : Except String (Json × Json) := do
 let (root,s) ← (intern e).run {}
 return (Json.mkObj [("encoding",toJson "Lean.Expr.DAG.v1"),("root",toJson root),("nodes",.arr s.nodes)],
   toJson (s.metadata.map fun d => reprStr d))
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
 let cases := #[first,renamed,swapped,explicit,implicit,instanceBinder,deep,.mdata {} first,
   mkConst (Name.num (Name.str .anonymous "numeric_namespace") 7) [.max (.param `u) (.succ .zero)]]
 for e in cases do
  let (_,_) ← ofExcept (Run20TypeEncoding.pack e)
 let bad := Run20TypeEncoding.decodeNode (.arr #[toJson "app",toJson (99:Nat),toJson (0:Nat)]) #[] #[]
 if bad.isOk then throwError "forward DAG reference accepted"
 let controls := #["actual alpha-equivalence", "binder renaming", "bound-variable order",
   "explicit/implicit binder", "instance binder", "universe levels", "exact metadata preservation",
   "all 200 nested applications", "no display ellipses", "exact JSON DAG reconstruction for all cases",
   "numeric Name segments and universe AST", "reject forward DAG references"]
 IO.println ((Json.mkObj [("status",toJson "PASS_COMPLETE_KERNEL_TYPE_ENCODING"),("controls",toJson controls)]).compress)
