module
public import NSP14.Homological.KoszulTor
public import Mathlib.LinearAlgebra.TensorProduct.Map
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace NSP14.Homological
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)

local instance : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
local instance : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm e.toRingHom e.symm.toRingHom

noncomputable def restrictedSemilinearEquiv (M : ModuleCat.{u} S) :
    (ModuleCat.restrictScalars e.toRingHom).obj M ≃ₛₗ[e.toRingHom] M where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def restrictTensorEquiv (M N : ModuleCat.{u} S) :
    ((tensoringLeft (ModuleCat R)).obj ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
      ((ModuleCat.restrictScalars e.toRingHom).obj N) ≃ₗ[R]
    (ModuleCat.restrictScalars e.toRingHom).obj (((tensoringLeft (ModuleCat S)).obj M).obj N) := by
  let t := TensorProduct.congr (restrictedSemilinearEquiv e M) (restrictedSemilinearEquiv e N)
  exact
    { toFun x := t x
      invFun y := t.symm y
      left_inv x := t.symm_apply_apply x
      right_inv y := t.apply_symm_apply y
      map_add' x y := t.map_add x y
      map_smul' r x := by
        change t (r • x)=e r • t x
        exact t.map_smulₛₗ r x }
theorem restrictTensorEquiv_tmul (M N : ModuleCat.{u} S)
    (m : (ModuleCat.restrictScalars e.toRingHom).obj M)
    (n : (ModuleCat.restrictScalars e.toRingHom).obj N) :
    restrictTensorEquiv e M N (m ⊗ₜ[R] n)=
      (show (ModuleCat.restrictScalars e.toRingHom).obj (((tensoringLeft (ModuleCat S)).obj M).obj N) from
        (show M from m) ⊗ₜ[S] (show N from n)) := rfl

noncomputable def restrictTensorNatIso (M : ModuleCat.{u} S) :
    ModuleCat.restrictScalars e.toRingHom ⋙
      (tensoringLeft (ModuleCat R)).obj ((ModuleCat.restrictScalars e.toRingHom).obj M) ≅
    (tensoringLeft (ModuleCat S)).obj M ⋙ ModuleCat.restrictScalars e.toRingHom :=
  NatIso.ofComponents (fun N => (restrictTensorEquiv e M N).toModuleIso) (by
    intro N N' g
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    change restrictTensorEquiv e M N' (m ⊗ₜ[R] (g n))=
      (TensorProduct.map (LinearMap.id) g.hom) (restrictTensorEquiv e M N (m ⊗ₜ[R] n))
    rw [restrictTensorEquiv_tmul,restrictTensorEquiv_tmul,TensorProduct.map_tmul]
    rfl)
end NSP14.Homological
