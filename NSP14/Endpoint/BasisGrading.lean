module
public import NSP14.Homological.CoordinateGrading
public import Mathlib.LinearAlgebra.Finsupp.Supported
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint
variable (k σ I : Type) [Field k] (M : ModuleCat.{0} (VariableRing k σ))
  (c : coefficientModule k σ M ≃ₗ[k] (I →₀ k)) (deg : I → ℤ)

/-- A homogeneous actual variable matrix on a genuine basis suffices
to assemble the actual grading; no grading of an unrelated model is used. -/
noncomputable def basisGrading
    (h : ∀ x p j,deg j≠deg p+1 →
      c ((MvPolynomial.X x : VariableRing k σ) • c.symm (Finsupp.single p 1)) j=0) :
    GradedPolynomialModule k σ M :=
  coordinateGrading k I deg σ M c (by
    intro x q a ha j hj
    let L : (I →₀ k) →ₗ[k] (I →₀ k) := c.toLinearMap.comp
      ((coefficientMap k σ (ModuleCat.ofHom (X:=M) (Y:=M) (variableOperator k σ M x))).comp c.symm.toLinearMap)
    have hmap : Finsupp.supported k k {p | deg p=q}≤
        (Finsupp.supported k k {p | deg p=q+1}).comap L := by
      rw [Finsupp.supported_eq_span_single]
      apply Submodule.span_le.mpr
      rintro _ ⟨p,hp,rfl⟩
      change L (Finsupp.single p 1)∈Finsupp.supported k k {p | deg p=q+1}
      rw [Finsupp.mem_supported']
      intro j hj
      change deg p=q at hp
      change deg j≠q+1 at hj
      exact h x p j (by rw [hp];exact hj)
    have hin : c a∈Finsupp.supported k k {p | deg p=q} := by
      rw [Finsupp.mem_supported']
      exact ha
    have hout := hmap hin
    change L (c a)∈Finsupp.supported k k {p | deg p=q+1} at hout
    rw [Finsupp.mem_supported'] at hout
    have hz := hout j hj
    change c ((MvPolynomial.X x : VariableRing k σ) • c.symm (c a)) j=0 at hz
    simpa only [LinearEquiv.symm_apply_apply] using hz)
end NSP14.Endpoint
