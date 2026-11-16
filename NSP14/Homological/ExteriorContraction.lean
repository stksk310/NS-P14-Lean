module
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
@[expose] public section
open scoped Classical
noncomputable section
namespace NSP14.Homological
variable (R : Type) [CommRing R] {M N : Type} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem exterior_contract_map (f : M →ₗ[R] N) (φ : Module.Dual R N) (x : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft φ (ExteriorAlgebra.map f x)=
      ExteriorAlgebra.map f (CliffordAlgebra.contractLeft (φ.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp only [AlgHom.commutes,CliffordAlgebra.contractLeft_algebraMap,map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | ι_mul m x hx =>
    simp only [map_mul,ExteriorAlgebra.map_apply_ι,CliffordAlgebra.contractLeft_ι_mul,
      map_sub,map_smul,LinearMap.comp_apply,hx]

def exteriorAlgebraLinearEquiv (e : M ≃ₗ[R] N) :
    ExteriorAlgebra R M ≃ₗ[R] ExteriorAlgebra R N where
  toFun := ExteriorAlgebra.map e.toLinearMap
  invFun := ExteriorAlgebra.map e.symm.toLinearMap
  left_inv := ExteriorAlgebra.leftInverse_map_iff.mpr e.left_inv
  right_inv := ExteriorAlgebra.leftInverse_map_iff.mpr e.right_inv
  map_add' := map_add _
  map_smul' := map_smul _

def exteriorPowerLinearEquiv (n : ℕ) (e : M ≃ₗ[R] N) : (⋀[R]^n M) ≃ₗ[R] (⋀[R]^n N) :=
  LinearEquiv.ofBijective (exteriorPower.map n e.toLinearMap)
    ⟨exteriorPower.map_injective e.symm.toLinearMap (by ext m; exact e.symm_apply_apply m),
      exteriorPower.map_surjective e.surjective⟩
end NSP14.Homological
