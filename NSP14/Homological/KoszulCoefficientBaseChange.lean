module

public import NSP14.Homological.FieldExtension

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]

/-- The actual Koszul complex viewed over its coefficient field; no chain finiteness assertion. -/
noncomputable def coefficientKoszulComplex (M : ModuleCat.{u} (VariableRing k σ)) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex
    (ComplexShape.down ℕ)).obj (koszulList k σ (variableList k σ) M)

noncomputable def coefficientKoszulHomologyIso (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) :
    (coefficientKoszulComplex k σ M).homology i ≅ koszulHomologyK k σ M i :=
  ((koszulList k σ (variableList k σ) M).sc i).mapHomologyIso
    (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ)))

noncomputable instance coefficientKoszulHomologyFinite (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    Module.Finite k ((coefficientKoszulComplex k σ M).homology i) := by
  let : Module.Finite k (koszulHomologyK k σ M i) := koszul_homology_finite k σ M i
  exact Module.Finite.equiv (coefficientKoszulHomologyIso k σ M i).symm.toLinearEquiv

variable (L : Type u) [Field L] [Algebra k L]

/-- Flat extension of the actual coefficient Koszul complex commutes with homology.
This is not yet an identification with Koszul over L[X]. -/
noncomputable def extendedCoefficientKoszulHomologyIso (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) :
    (((fieldExtension k L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (coefficientKoszulComplex k σ M)).homology i ≅
        (fieldExtension k L).obj (koszulHomologyK k σ M i) :=
  fieldExtensionHomologyIso k L _ i ≪≫
    (fieldExtension k L).mapIso (coefficientKoszulHomologyIso k σ M i)

theorem extendedCoefficientKoszul_finrank (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    Module.finrank L ((((fieldExtension k L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (coefficientKoszulComplex k σ M)).homology i) = totalBetti k σ M i :=
  (extendedCoefficientKoszulHomologyIso k σ L M i).toLinearEquiv.finrank_eq.trans
    (fieldExtension_finrank k L _)

end NSP14.Homological
