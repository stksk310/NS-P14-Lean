module

public import NSP14.Homological.Betti

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]

/-- Coefficient restriction of the augmentation module is the original coefficient field. -/
noncomputable def residueCoefficientIso :
    (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).obj (residueField k σ) ≅ ModuleCat.of k k := by
  let e : ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).obj (residueField k σ)) ≃ₗ[k] k :=
    { toFun := fun a => a
      invFun := fun a => a
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun c a => by
        change augmentation k σ (algebraMap k (VariableRing k σ) c) * (show k from a) = c*(show k from a)
        rw [(augmentation k σ).commutes]
        rfl }
  exact e.toModuleIso

noncomputable def koszulFreeH0Iso :
    koszulHomologyK k σ (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) 0 ≅ ModuleCat.of k k := by
  let : QuasiIso (koszulAugmentation k σ) := koszulAugmentation_quasiIso k σ
  let e := isoOfQuasiIsoAt (koszulAugmentation k σ) 0 ≪≫
    singleObjHomologySelfIso (ComplexShape.down ℕ) 0 (residueField k σ)
  exact (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso e ≪≫ residueCoefficientIso k σ

theorem totalBetti_free_zero :
    totalBetti k σ (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) 0=1 := by
  exact (koszulFreeH0Iso k σ).toLinearEquiv.finrank_eq.trans (Module.finrank_self k)

theorem totalBetti_free_succ (i : ℕ) :
    totalBetti k σ (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) (i+1)=0 := by
  have hz := (koszul_polynomial_exact_positive k σ (variableList k σ) (variableList_nodup k σ) i).isZero_homology
  have : Subsingleton (koszulHomologyK k σ (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) (i+1)) :=
    (show Subsingleton (koszulHomology k σ (variableList k σ)
      (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) (i+1)) from ModuleCat.subsingleton_of_isZero hz)
  exact Module.finrank_zero_of_subsingleton

end NSP14.Homological
