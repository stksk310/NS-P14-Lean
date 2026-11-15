module
public import NSP14.Homological.FunctionalMinor
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Order.Prod.Lex.Basic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Homological
variable (k : Type) [Field k] {ι X Y : Type} [Fintype ι] [LinearOrder ι]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] [Module.Finite k Y]

/-- The ranks of the actual diagonal blocks of an upper triangular linear map
sum to at most its actual rank. No source finiteness is required. -/
theorem triangular_block_rank (d : X →ₗ[k] Y) (U : ι → Submodule k X)
    (P : ι → Y →ₗ[k] Y) (htri : ∀ a b, b<a → ∀ x : U b,P a (d x)=0) :
    (∑ a,Module.finrank k ((P a).comp (d.comp (U a).subtype)).range) ≤ Module.finrank k d.range := by
  let B (a : ι) := (P a).comp (d.comp (U a).subtype)
  let basis (a : ι) := Module.finBasis k (B a).range
  let J := (a : ι) × Fin (Module.finrank k (B a).range)
  let columns : J → X := fun j => ((basis j.1 j.2).property.choose : U j.1)
  let rows : J → Y →ₗ[k] k := fun j =>
    ((basis j.1).coord j.2).comp ((B j.1).range.subtype.leftInverse.comp (P j.1))
  have hcol (j : J) : P j.1 (d (columns j))=(basis j.1 j.2).val := by
    exact (basis j.1 j.2).property.choose_spec
  have heq (a : ι) (i j : Fin (Module.finrank k (B a).range)) :
      rows ⟨a,i⟩ (d (columns ⟨a,j⟩))=if j=i then 1 else 0 := by
    change (basis a).coord i ((B a).range.subtype.leftInverse (P a (d (columns ⟨a,j⟩))))=_
    rw [hcol ⟨a,j⟩]
    change (basis a).coord i ((B a).range.subtype.leftInverse ((B a).range.subtype (basis a j)))=_
    have he := LinearMap.leftInverse_apply_of_inj (B a).range.ker_subtype (basis a j)
    rw [he]
    exact (basis a).repr_self_apply j i
  let key : J → ι ×ₗ Fin (Fintype.card J) := fun a => toLex (a.1,Fintype.equivFin J a)
  have hk : Function.Injective key := by
    intro a b he
    exact (Fintype.equivFin J).injective (congrArg (fun z => (ofLex z).2) he)
  let : LinearOrder J := LinearOrder.lift' key hk
  have hr : Fintype.card J ≤ Module.finrank k d.range := by
    apply triangular_functional_minor_rank_lower_bound k d columns rows
    · intro a b hba
      have hne : a ≠ b := ne_of_gt hba
      change key b < key a at hba
      rw [Prod.Lex.lt_iff] at hba
      rcases hba with hlt|⟨he,_⟩
      · change (basis a.1).coord a.2 ((B a.1).range.subtype.leftInverse (P a.1 (d (columns b))))=0
        rw [htri a.1 b.1 hlt ((basis b.1 b.2).property.choose)]
        simp only [map_zero]
      · rcases a with ⟨a,i⟩
        rcases b with ⟨b,j⟩
        change b=a at he
        subst b
        change rows ⟨a,i⟩ (d (columns ⟨a,j⟩))=0
        rw [heq a i j]
        exact ite_eq_right (fun hij => hne (by subst j; rfl))
    · intro a
      exact Or.inl (by rw [heq]; exact ite_eq_left rfl)
  simpa only [J,Fintype.card_sigma,Fintype.card_fin] using hr
end NSP14.Homological
