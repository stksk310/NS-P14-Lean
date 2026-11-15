module
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
@[expose] public section
open scoped Classical TensorProduct
noncomputable section
namespace NSP14.Homological
variable {k M V J : Type} [Field k] [AddCommGroup M] [Module k M]
  [AddCommGroup V] [Module k V]

def basiswiseTensorEquiv (b : Module.Basis J k M) (e : J → V ≃ₗ[k] V) :
    M ⊗[k] V ≃ₗ[k] M ⊗[k] V :=
  (TensorProduct.equivFinsuppOfBasisLeft b).trans
    ((finsuppLequivDFinsupp k).trans
      ((DFinsupp.mapRange.linearEquiv e).trans
        ((finsuppLequivDFinsupp k).symm.trans
          (TensorProduct.equivFinsuppOfBasisLeft b).symm)))

theorem basiswiseTensorEquiv_coordinates (b : Module.Basis J k M) (e : J → V ≃ₗ[k] V)
    (t : M ⊗[k] V) (j : J) :
    TensorProduct.equivFinsuppOfBasisLeft b (basiswiseTensorEquiv b e t) j =
      e j (TensorProduct.equivFinsuppOfBasisLeft b t j) := by
  simp only [basiswiseTensorEquiv,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply]
  rfl

theorem basiswiseTensorEquiv_tmul (b : Module.Basis J k M) (e : J → V ≃ₗ[k] V)
    (j : J) (w : V) :
    basiswiseTensorEquiv b e (b j ⊗ₜ[k] w)=b j ⊗ₜ[k] e j w := by
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  ext i
  rw [basiswiseTensorEquiv_coordinates,TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply,Module.Basis.repr_self]
  by_cases hi : i=j
  · subst i
    simp only [Finsupp.single_eq_same,one_smul]
  · simp only [Finsupp.single_eq_of_ne hi,zero_smul,map_zero]
end NSP14.Homological
