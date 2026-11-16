module
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section
open scoped BigOperators Classical
namespace NSP14.Homological
variable (k : Type*) [Field k] (d n : ℕ)

/-- Finite Hankel action on an actual lower/upper coefficient pair. -/
noncomputable def hankelAction (j : ℕ) :
    ((Fin d → k) × (Fin n → k)) →ₗ[k] ((Fin d → k) × (Fin n → k)) where
  toFun p := (0,fun b => ∑ a : Fin d,(if j=a.val+b.val then (1:k) else 0)*p.1 a)
  map_add' p q := by
    apply Prod.ext
    · change (0 : Fin d → k)=0+0
      simp
    · funext b
      simp only [Prod.fst_add,Prod.snd_add,Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' c p := by
    apply Prod.ext
    · change (0 : Fin d → k)=c • 0
      simp
    · funext b
      change (∑ a : Fin d,(if j=a.val+b.val then (1:k) else 0)*(c*p.1 a))=
        c*(∑ a : Fin d,(if j=a.val+b.val then (1:k) else 0)*p.1 a)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
end NSP14.Homological
