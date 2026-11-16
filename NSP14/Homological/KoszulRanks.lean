module

public import NSP14.Homological.KoszulLongExact
public import NSP14.Homological.KoszulCoefficientBaseChange

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]
variable (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))

noncomputable def coefficientKoszulSequence : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  (S.map (koszulFunctor k σ (variableList k σ))).map
    ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _)

theorem coefficientKoszulSequence_shortExact (hS : S.ShortExact) :
    (coefficientKoszulSequence k σ S).ShortExact := by
  have hK := koszul_shortExact k σ (variableList k σ) S hS
  let : Mono (S.map (koszulFunctor k σ (variableList k σ))).f := hK.mono_f
  let : Epi (S.map (koszulFunctor k σ (variableList k σ))).g := hK.epi_g
  exact hK.map _

noncomputable instance coefficientKoszulSequence_finite₁ [Module.Finite (VariableRing k σ) S.X₁] (i : ℕ) :
    Module.Finite k ((coefficientKoszulSequence k σ S).X₁.homology i) := by
  change Module.Finite k ((coefficientKoszulComplex k σ S.X₁).homology i)
  infer_instance
noncomputable instance coefficientKoszulSequence_finite₂ [Module.Finite (VariableRing k σ) S.X₂] (i : ℕ) :
    Module.Finite k ((coefficientKoszulSequence k σ S).X₂.homology i) := by
  change Module.Finite k ((coefficientKoszulComplex k σ S.X₂).homology i)
  infer_instance
noncomputable instance coefficientKoszulSequence_finite₃ [Module.Finite (VariableRing k σ) S.X₃] (i : ℕ) :
    Module.Finite k ((coefficientKoszulSequence k σ S).X₃.homology i) := by
  change Module.Finite k ((coefficientKoszulComplex k σ S.X₃).homology i)
  infer_instance

/-- Correction rank of the actual connecting map, with its original homological indices. -/
noncomputable def koszulCorrectionRank (hS : S.ShortExact) (i : ℕ) : ℕ :=
  Module.finrank k ((coefficientKoszulSequence_shortExact k σ S hS).δ (i+1) i rfl).hom.range

variable [Module.Finite (VariableRing k σ) S.X₁]
  [Module.Finite (VariableRing k σ) S.X₂] [Module.Finite (VariableRing k σ) S.X₃]

theorem koszul_betti_rank_correction (hS : S.ShortExact) (i : ℕ) :
    totalBetti k σ S.X₂ (i+1)+koszulCorrectionRank k σ S hS i+
      koszulCorrectionRank k σ S hS (i+1)=
    totalBetti k σ S.X₁ (i+1)+totalBetti k σ S.X₃ (i+1) := by
  have h := homology_rank_correction k _ (coefficientKoszulSequence_shortExact k σ S hS) i
  change Module.finrank k ((coefficientKoszulComplex k σ S.X₂).homology (i+1)) + _ + _ =
    Module.finrank k ((coefficientKoszulComplex k σ S.X₁).homology (i+1)) +
      Module.finrank k ((coefficientKoszulComplex k σ S.X₃).homology (i+1)) at h
  rw [(coefficientKoszulHomologyIso k σ S.X₂ (i+1)).toLinearEquiv.finrank_eq,
    (coefficientKoszulHomologyIso k σ S.X₁ (i+1)).toLinearEquiv.finrank_eq,
    (coefficientKoszulHomologyIso k σ S.X₃ (i+1)).toLinearEquiv.finrank_eq] at h
  exact h

theorem koszul_betti_rank_correction_zero (hS : S.ShortExact) :
    totalBetti k σ S.X₂ 0+koszulCorrectionRank k σ S hS 0=
      totalBetti k σ S.X₁ 0+totalBetti k σ S.X₃ 0 := by
  have h := homology_rank_correction_zero k _ (coefficientKoszulSequence_shortExact k σ S hS)
  change Module.finrank k ((coefficientKoszulComplex k σ S.X₂).homology 0) + _ =
    Module.finrank k ((coefficientKoszulComplex k σ S.X₁).homology 0) +
      Module.finrank k ((coefficientKoszulComplex k σ S.X₃).homology 0) at h
  rw [(coefficientKoszulHomologyIso k σ S.X₂ 0).toLinearEquiv.finrank_eq,
    (coefficientKoszulHomologyIso k σ S.X₁ 0).toLinearEquiv.finrank_eq,
    (coefficientKoszulHomologyIso k σ S.X₃ 0).toLinearEquiv.finrank_eq] at h
  exact h

end NSP14.Homological
