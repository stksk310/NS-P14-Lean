module

public import NSP14.Homological.KoszulTorNaturality
public import NSP14.Homological.KoszulFree
public import NSP14.Homological.PolynomialBaseChangeModule
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.LinearAlgebra.TensorProduct.Basis

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]

noncomputable def flatKoszulHomologyIso (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Flat (VariableRing k σ) M] (i : ℕ) :
    koszulHomology k σ (variableList k σ) M i ≅
      ((tensoringLeft _).obj M).obj
        (koszulHomology k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) i) :=
  ((homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (tensorKoszulIso k σ (variableList k σ) M)).symm ≪≫
    ((koszulList k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).sc i).mapHomologyIso
      ((tensoringLeft _).obj M)

theorem freeKoszulHomology_positive (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Free (VariableRing k σ) M] (i : ℕ) :
    IsZero (koszulHomology k σ (variableList k σ) M (i+1)) := by
  have hz := (koszul_polynomial_exact_positive k σ (variableList k σ) (variableList_nodup k σ) i).isZero_homology
  exact IsZero.of_iso (((tensoringLeft _).obj M).map_isZero hz) (flatKoszulHomologyIso k σ M (i+1))

noncomputable def freeKoszulH0TensorIso (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Free (VariableRing k σ) M] :
    koszulHomology k σ (variableList k σ) M 0 ≅ ((tensoringLeft _).obj M).obj (residueField k σ) := by
  let : QuasiIso (koszulAugmentation k σ) := koszulAugmentation_quasiIso k σ
  exact flatKoszulHomologyIso k σ M 0 ≪≫ ((tensoringLeft _).obj M).mapIso
    (isoOfQuasiIsoAt (koszulAugmentation k σ) 0 ≪≫ singleObjHomologySelfIso _ 0 (residueField k σ))

/-- An actual finite free basis yields the rank of zeroth Koszul homology. -/
noncomputable def freeKoszulH0BasisIso {ι : Type u} (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Free (VariableRing k σ) M] (b : Module.Basis ι (VariableRing k σ) M) :
    koszulHomologyK k σ M 0 ≅ ModuleCat.of k (ι →₀ k) := by
  classical
  let e := (TensorProduct.comm (VariableRing k σ) M (residueField k σ)).trans
    (TensorProduct.equivFinsuppOfBasisRight b)
  let eP : ((tensoringLeft (ModuleCat (VariableRing k σ))).obj M).obj (residueField k σ) ≅
      ModuleCat.of (VariableRing k σ) (ι →₀ residueField k σ) := e.toModuleIso
  let eC := (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso
    (freeKoszulH0TensorIso k σ M ≪≫ eP)
  exact eC ≪≫ (Finsupp.mapRange.linearEquiv (residueCoefficientIso k σ).toLinearEquiv).toModuleIso

theorem minimalFreeRank_at_zero {ι : Type u} [Fintype ι] (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Free (VariableRing k σ) M] [Module.Finite (VariableRing k σ) M]
    (b : Module.Basis ι (VariableRing k σ) M) : totalBetti k σ M 0=Fintype.card ι := by
  rw [totalBetti,(freeKoszulH0BasisIso k σ M b).toLinearEquiv.finrank_eq]
  exact Module.finrank_finsupp_self k

end NSP14.Homological
