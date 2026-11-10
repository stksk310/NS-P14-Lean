module
public import NSP14.Homological.KoszulListResolution
public import NSP14.Homological.BettiEuler
public import NSP14.Homological.ComplexEuler
public import NSP14.Homological.KoszulCoefficientBaseChange
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]
  (xs : List σ) (hall : ∀ x : σ,x ∈ xs) (hxs : xs.Nodup)
  (M : ModuleCat.{u} (VariableRing k σ))

noncomputable def fullListHomologyKIso (i : ℕ) :
    koszulHomologyK k σ M i ≅
      (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (koszulList k σ xs M)).homology i :=
  (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso
    ((torKoszulIso k σ M i).symm ≪≫ fullListTorKoszulIso k σ xs hall hxs M i) ≪≫
      (((koszulList k σ xs M).sc i).mapHomologyIso
        (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ)))).symm

include hall hxs in
theorem fullList_totalBetti [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    totalBetti k σ M i=Module.finrank k
      ((((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (koszulList k σ xs M)).homology i) :=
  (fullListHomologyKIso k σ xs hall hxs M i).toLinearEquiv.finrank_eq

include hall hxs in
theorem fullList_complexEuler [Module.Finite (VariableRing k σ) M] (j : ℕ) :
    complexEuler k (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (koszulList k σ xs M)) j=bettiEuler k σ M j := by
  unfold complexEuler bettiEuler
  congr 1
  funext i
  exact (fullList_totalBetti k σ xs hall hxs M i).symm
end NSP14.Homological
