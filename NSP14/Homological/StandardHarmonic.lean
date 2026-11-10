module
public import NSP14.Homological.KoszulWeightedRank
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ] [Nonempty σ]
  (M : ModuleCat.{u} (VariableRing k σ)) (m : MonomialOrder σ)
  {q : ℕ} (g : Fin q → coefficientModule k σ M)
  (hg : Submodule.span (VariableRing k σ) (Set.range g)=⊤)
  [Fintype (ModuleStandard k m g)] [Module.Finite k (coefficientModule k σ M)]
  [Module.Finite (VariableRing k σ) M]

include hg in
/-- Finite actual Koszul Euler plus the constructed signed-unit minor.
This statement already covers arbitrary numbers of module generators. -/
theorem standard_harmonic_bound (j : ℕ) (hj : 0 < j) :
    (bettiEuler k σ M j : ℚ) ≤ ((Fintype.card σ-1).choose j : ℚ)*
      ∑ i : ModuleStandard k m g,(j : ℚ)/((moduleTermExponent m i.val).degree+j) := by
  let d : ModuleStandard k m g → ℕ := fun i => (moduleTermExponent m i.val).degree
  have hsplit : (∑ i : ModuleStandard k m g,(j : ℚ)/(d i+j))+
      (∑ i : ModuleStandard k m g,(d i : ℚ)/(d i+j))=
        Module.finrank k (coefficientModule k σ M) := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : ModuleStandard k m g,(1:ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        have hz : (d i+j : ℚ) ≠ 0 := ne_of_gt
          (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (Nat.cast_pos.mpr hj))
        rw [← add_div,add_comm (j : ℚ),div_self hz]
      _ = _ := by simp [Module.finrank_eq_card_basis (moduleStandardBasis k m g hg)]
  have hr : 1 ≤ Fintype.card σ := Fintype.card_pos
  have he : (bettiEuler k σ M j : ℚ)=((Fintype.card σ-1).choose j : ℚ)*
      Module.finrank k (coefficientModule k σ M)-(koszulBoundaryRank k σ M (j+1) : ℚ) := by
    exact_mod_cast finite_koszul_bettiEuler k σ M hr j
  have hb := standardKoszul_boundary_lower k σ M m g hg j hj
  change ((Fintype.card σ-1).choose j : ℚ)*(∑ i : ModuleStandard k m g,(d i : ℚ)/(d i+j)) ≤ _ at hb
  change (bettiEuler k σ M j : ℚ) ≤ ((Fintype.card σ-1).choose j : ℚ)*
    ∑ i : ModuleStandard k m g,(j : ℚ)/(d i+j)
  rw [he]
  nlinarith
end NSP14.Homological
