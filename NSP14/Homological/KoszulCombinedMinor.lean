module
public import NSP14.Homological.KoszulIndependentImages
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Classical BigOperators
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]
  (M : ModuleCat.{u} (VariableRing k σ))
  [Module.Finite k (coefficientModule k σ M)]
  (u₀ : coefficientModule k σ M)
  (ρ : σ → coefficientModule k σ M →ₗ[k] k)
  (hρ : ∀ v w,ρ v ((MvPolynomial.X w : VariableRing k σ) • u₀)=if v=w then 1 else 0)

include hρ in
/-- Two actual differential minors in disjoint coefficient degrees combine.
All entries are evaluated in the same Koszul differential; no Betti
comparison is supplied as an assumption. -/
theorem koszulBoundaryRank_ge_choose_add {ι : Type u} [Fintype ι] (j : ℕ)
    (columns : ι → (coefficientKoszulComplex k σ M).X (j+1))
    (rows : ι → (coefficientKoszulComplex k σ M).X j →ₗ[k] k)
    (hdiag : ∀ a,rows a (((coefficientKoszulComplex k σ M).d (j+1) j).hom (columns a))=1 ∨
      rows a (((coefficientKoszulComplex k σ M).d (j+1) j).hom (columns a))= -1)
    (hoff : ∀ a b,a≠b → rows a (((coefficientKoszulComplex k σ M).d (j+1) j).hom (columns b))=0)
    (hupper : ∀ s a,koszulImageRow k σ M ρ j s
      (((coefficientKoszulComplex k σ M).d (j+1) j).hom (columns a))=0)
    (hlower : ∀ a s,rows a (((coefficientKoszulComplex k σ M).d (j+1) j).hom
      (koszulUnitColumn k σ M u₀ j s))=0) :
    (Fintype.card σ).choose (j+1)+Fintype.card ι ≤ koszulBoundaryRank k σ M (j+1) := by
  let C := Sum.elim (koszulUnitColumn k σ M u₀ j) columns
  let R := Sum.elim (koszulImageRow k σ M ρ j) rows
  let A : Matrix (KoszulSlot (variableList k σ).length (j+1) ⊕ ι)
      (KoszulSlot (variableList k σ).length (j+1) ⊕ ι) k :=
    fun a b => R a (((coefficientKoszulComplex k σ M).d (j+1) j).hom (C b))
  have hA : A=Matrix.diagonal (fun a => A a a) := by
    ext a b
    by_cases he : a=b
    · subst b
      simp
    · rw [Matrix.diagonal_apply,ite_eq_right he]
      cases a with
      | inl s => cases b with
        | inl t => exact koszulImageEntry_offDiagonal k σ M u₀ ρ hρ j s t (by simpa using he)
        | inr b => exact hupper s b
      | inr a => cases b with
        | inl t => exact hlower a t
        | inr b => exact hoff a b (by simpa using he)
  have hdet : Matrix.det A≠0 := by
    rw [hA,Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    cases a with
    | inl s =>
      rcases koszulImageEntry_diag k σ M u₀ ρ hρ j s with h|h <;>
        simp only [A,R,C,Sum.elim_inl,h] <;> simp
    | inr a =>
      rcases hdiag a with h|h <;>
        simp only [A,R,C,Sum.elim_inr,h] <;> simp
  let : Module.Finite k ((coefficientKoszulComplex k σ M).X j) :=
    koszul_chain_coefficient_finite k σ (variableList k σ) M j
  have h := functional_minor_rank_lower_bound k ((coefficientKoszulComplex k σ M).d (j+1) j).hom C R hdet
  rw [Fintype.card_sum,koszulSlot_card,variableList_length] at h
  simpa only [koszulBoundaryRank,chainBoundaryRank_succ] using h
end NSP14.Homological
