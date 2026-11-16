module
public import NSP14.Homological.KoszulH0Naturality
public import NSP14.Homological.KoszulZeroAction
public import NSP14.Homological.Betti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

omit [Fintype σ] in
theorem koszulZeroMap_epi (xs : List σ) {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N) [Epi f] :
    Epi (((koszulFunctor k σ xs).map f).f 0) := by
  have h := koszulZeroIso_naturality k σ xs f
  have he : ((koszulFunctor k σ xs).map f).f 0=(koszulZeroIso k σ xs M).hom ≫ f ≫ (koszulZeroIso k σ xs N).inv := by
    rw [← Category.assoc,← h,Category.assoc,Iso.hom_inv_id,Category.comp_id]
  rw [he]
  infer_instance

/-- H0 is right exact for the actual variable complex, with no finite
chain-group assumption. -/
theorem koszulHomologyZeroMap_epi {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N) [Epi f] :
    Epi ((koszulHomologyFunctor k σ (variableList k σ) 0).map f) := by
  let : Epi (((koszulFunctor k σ (variableList k σ)).map f).f 0) := koszulZeroMap_epi k σ _ f
  exact epi_homologyMap_of_epi_of_not_rel ((koszulFunctor k σ (variableList k σ)).map f) 0
    (by intro j h;change j+1=0 at h;omega)

theorem totalBetti_zero_le_of_epi {M N : ModuleCat.{u} (VariableRing k σ)}
    [Module.Finite (VariableRing k σ) M] [Module.Finite (VariableRing k σ) N] (f : M ⟶ N) [Epi f] :
    totalBetti k σ N 0≤totalBetti k σ M 0 := by
  let := koszul_homology_finite k σ M 0
  let : Epi ((koszulHomologyFunctor k σ (variableList k σ) 0).map f) := koszulHomologyZeroMap_epi k σ f
  let g : koszulHomologyK k σ M 0 ⟶ koszulHomologyK k σ N 0 :=
    (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).map
      ((koszulHomologyFunctor k σ (variableList k σ) 0).map f)
  let : Epi g := inferInstance
  exact LinearMap.finrank_le_finrank_of_surjective ((ModuleCat.epi_iff_surjective g).mp inferInstance)

/-- The actual residue module has the expected zeroth ordinary Tor rank. -/
theorem residueField_totalBetti_zero [Module.Finite (VariableRing k σ) (residueField k σ)] :
    totalBetti k σ (residueField k σ) 0=1 := by
  let eP := koszulHomologyZeroActionIso k σ (variableList k σ) (residueField k σ)
    (fun x _ a => residueField_variable k σ x a) 0 ≪≫ koszulZeroIso k σ _ (residueField k σ)
  let eK := (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso eP
  have h := eK.toLinearEquiv.finrank_eq
  have e : (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).obj (residueField k σ) ≃ₗ[k] k :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' c a := by
        change augmentation k σ (algebraMap k (VariableRing k σ) c)*(show k from a)=c*(show k from a)
        rw [(augmentation k σ).commutes]
        rfl }
  exact h.trans (e.finrank_eq.trans (Module.finrank_self k))
end NSP14.Homological
