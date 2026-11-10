module
public import Mathlib.LinearAlgebra.Pi
@[expose] public section
open scoped Classical
namespace NSP14.Homological
variable (k : Type*) [Field k] (v d : ℕ) (hd : d ≤ v)

noncomputable def reverseWindowSplit : (Fin v → k) ≃ₗ[k] ((Fin d → k) × (Fin (v-d) → k)) where
  toFun f :=
    (fun a => f ⟨d-1-a.val,by have := a.isLt;omega⟩,
     fun b => f ⟨d+b.val,by have := b.isLt;omega⟩)
  invFun p a := if h : a.val<d then p.1 ⟨d-1-a.val,by omega⟩ else p.2 ⟨a.val-d,by have := a.isLt;omega⟩
  left_inv f := by
    funext a
    dsimp only
    split_ifs with ha
    · apply congrArg f
      apply Fin.ext
      change d-1-(d-1-a.val)=a.val
      omega
    · apply congrArg f
      apply Fin.ext
      change d+(a.val-d)=a.val
      omega
  right_inv p := by
    apply Prod.ext
    · funext a
      dsimp only
      rw [dite_eq_left (by have := a.isLt;omega)]
      apply congrArg p.1
      apply Fin.ext
      change d-1-(d-1-a.val)=a.val
      have hi := a.isLt
      omega
    · funext b
      dsimp only
      rw [dite_eq_right (by omega)]
      apply congrArg p.2
      apply Fin.ext
      change d+b.val-d=b.val
      omega
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end NSP14.Homological
