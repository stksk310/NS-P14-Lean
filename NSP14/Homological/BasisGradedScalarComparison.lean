module
public import NSP14.Homological.GradedScalarComparison
public import NSP14.Homological.HomogeneousBasisPieces
public import Mathlib.LinearAlgebra.TensorProduct.Basis
@[expose] public section
open scoped Classical TensorProduct
open CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Homological
variable (k L σ : Type) [Field k] [Field L] [Algebra k L]

def basisGradedScalarComparison
    (M : ModuleCat (VariableRing k σ)) (N : ModuleCat (VariableRing L σ))
    (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule L σ N) {J : Type}
    (b : Module.Basis J k (coefficientModule k σ M))
    (c : Module.Basis J L (coefficientModule L σ N)) (deg : J → ℤ)
    (hb : ∀ j,b j∈G.degreeSpace (deg j)) (hc : ∀ j,c j∈H.degreeSpace (deg j))
    (e : polynomialBaseChangeModule k L σ M ≅ N)
    (he : ∀ j,(show coefficientModule L σ N from e.hom ((1:L) ⊗ₜ[k] b j))=c j) :
    GradedScalarComparison k L σ G H e where
  pieceIso q := ((homogeneousPieceBasis k σ M G b deg hb q).baseChange L).repr.trans
    (homogeneousPieceBasis L σ N H c deg hc q).repr.symm
  inclusion_commutes q a := by
    let bp := homogeneousPieceBasis k σ M G b deg hb q
    let cp := homogeneousPieceBasis L σ N H c deg hc q
    let ep := (bp.baseChange L).repr.trans cp.repr.symm
    let et : (L ⊗[k] coefficientModule k σ M) →ₗ[L] coefficientModule L σ N :=
      (coefficientMap L σ e.hom).comp (polynomialBaseChangeCoefficientIso k L σ M).symm.toLinearEquiv.toLinearMap
    let f : (L ⊗[k] G.piece q) →ₗ[L] coefficientModule L σ N := (H.inclusion q).comp ep.toLinearMap
    let g : (L ⊗[k] G.piece q) →ₗ[L] coefficientModule L σ N := et.comp ((G.inclusion q).baseChange L)
    have hfg : f=g := by
      apply (bp.baseChange L).ext
      intro j
      rw [Module.Basis.baseChange_apply]
      change H.inclusion q (ep ((1:L) ⊗ₜ[k] bp j))=
        et ((G.inclusion q).baseChange L ((1:L) ⊗ₜ[k] bp j))
      have hep : ep ((1:L) ⊗ₜ[k] bp j)=cp j := by
        change cp.repr.symm ((bp.baseChange L).repr ((1:L) ⊗ₜ[k] bp j))=cp j
        rw [← Module.Basis.baseChange_apply L bp j,Module.Basis.repr_self,Module.Basis.repr_symm_single_one]
      have hbp : G.inclusion q (bp j)=b j.val := homogeneousPieceBasis_inclusion k σ M G b deg hb q j
      have hcp : H.inclusion q (cp j)=c j.val := homogeneousPieceBasis_inclusion L σ N H c deg hc q j
      rw [hep,hcp,LinearMap.baseChange_tmul,hbp]
      change c j.val=e.hom ((1:L) ⊗ₜ[k] b j.val)
      exact (he j.val).symm
    have h := LinearMap.congr_fun hfg ((1:L) ⊗ₜ[k] a)
    change H.inclusion q (ep ((1:L) ⊗ₜ[k] a))=
      et ((G.inclusion q).baseChange L ((1:L) ⊗ₜ[k] a)) at h
    rw [LinearMap.baseChange_tmul] at h
    exact h
end NSP14.Homological
