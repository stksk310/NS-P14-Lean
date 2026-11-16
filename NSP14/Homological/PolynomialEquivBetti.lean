module
public import NSP14.Homological.ActionCoefficient
public import NSP14.Homological.Betti
public import NSP14.Homological.KoszulLongExact
public import NSP14.Homological.RingEquivTor
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Homological
universe u
variable (k τ σ : Type u) [Field k] [Fintype τ] [Fintype σ]
  (e : VariableRing k τ ≃ₐ[k] VariableRing k σ)
  (he : (augmentation k σ).comp e.toAlgHom=augmentation k τ)

noncomputable def polynomialEquivResidueIso :
    (ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj (residueField k σ) ≅ residueField k τ := by
  let l : (ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj (residueField k σ) ≃ₗ[VariableRing k τ] residueField k τ :=
    { toFun a := a
      invFun a := a
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' p a := by
        change augmentation k σ (e p)*(show k from a)=augmentation k τ p*(show k from a)
        have h := AlgHom.congr_fun he p
        change augmentation k σ (e p)=augmentation k τ p at h
        rw [h] }
  exact l.toModuleIso

noncomputable def polynomialEquivBettiIso (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) :
    koszulHomologyK k τ ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj M) i ≅
      koszulHomologyK k σ M i := by
  let F := ModuleCat.restrictScalars e.toRingEquiv.toRingHom
  let C := ModuleCat.restrictScalars (algebraMap k (VariableRing k τ))
  exact (torCoefficientIso k τ (F.obj M) i).symm ≪≫
    C.mapIso (((CategoryTheory.Tor (ModuleCat (VariableRing k τ)) i).obj (F.obj M)).mapIso
      (polynomialEquivResidueIso k τ σ e he).symm) ≪≫
    C.mapIso (ringEquivTorIso e.toRingEquiv M (residueField k σ) i) ≪≫
    (algebraRestrictionCoefficientEquiv k (VariableRing k τ) (VariableRing k σ) e.toAlgHom _).toModuleIso ≪≫
    torCoefficientIso k σ M i
omit [Fintype τ] [Fintype σ] in
theorem polynomialEquivRestricted_finite (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] :
    Module.Finite (VariableRing k τ) ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj M) := by
  let F := ModuleCat.restrictScalars e.toRingEquiv.toRingHom
  let : Module.Finite (VariableRing k σ) (F.obj M) := inferInstanceAs (Module.Finite (VariableRing k σ) M)
  exact finite_of_action_reduction (VariableRing k σ) (VariableRing k τ) (F.obj M) e.symm
    (by intro p m;change p • (show M from m)=e (e.symm p) • (show M from m);rw [e.apply_symm_apply])

include he in
theorem polynomialEquiv_totalBetti (M : ModuleCat.{u} (VariableRing k σ))
    [Module.Finite (VariableRing k σ) M] (i : ℕ) :
    letI := polynomialEquivRestricted_finite k τ σ e M
    totalBetti k τ ((ModuleCat.restrictScalars e.toRingEquiv.toRingHom).obj M) i=totalBetti k σ M i := by
  let := polynomialEquivRestricted_finite k τ σ e M
  exact (polynomialEquivBettiIso k τ σ e he M i).toLinearEquiv.finrank_eq
end NSP14.Homological
