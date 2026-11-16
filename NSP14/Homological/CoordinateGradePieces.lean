module

public import NSP14.Homological.CoordinateGrading
public import NSP14.Homological.CoordinateBaseChange

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

namespace NSP14.Homological

universe u
variable (k : Type u) [Field k] (I : Type u) (deg : I → ℤ)
variable (σ : Type u) (M : ModuleCat.{u} (VariableRing k σ))
variable (c : coefficientModule k σ M ≃ₗ[k] (I →₀ k))

theorem coordinateDegreeInclusion_coordinate (q : ℤ) (a : {i : I // deg i=q} →₀ k) (i : I) :
    c (coordinateDegreeInclusion k I deg σ M c q a) i =
      if h : deg i=q then a ⟨i,h⟩ else 0 := by
  classical
  by_cases h : deg i=q
  · rw [dite_eq_left h]
    have he := coordinateDegreeEquiv_apply k I deg
      (c (coordinateDegreeInclusion k I deg σ M c q a)) q ⟨i,h⟩
    simpa [coordinateDegreeInclusion] using he.symm
  · rw [dite_eq_right h]
    exact (coordinateDegreeInclusion_range k I deg σ M c q _).mp ⟨a,rfl⟩ i h

variable (L : Type u) [Field L] [Algebra k L]
variable (N : ModuleCat.{u} (VariableRing L σ))
variable (d : coefficientModule L σ N ≃ₗ[L] (I →₀ L))

/-- Coordinate expression of the already specified actual polynomial coefficient change. -/
theorem coordinateBaseChangePolynomialIso_tmul
    (hm : ∀ (x : σ) (i j : I),
      d ((MvPolynomial.X x : VariableRing L σ) • d.symm (Finsupp.single i 1)) j=
        algebraMap k L (c ((MvPolynomial.X x : VariableRing k σ) • c.symm (Finsupp.single i 1)) j))
    (l : L) (m : coefficientModule k σ M) (i : I) :
    d ((coordinateBaseChangePolynomialIso k L σ I M N c d hm).hom (l ⊗ₜ[k] m)) i=
      algebraMap k L (c m i)*l := by
  exact coordinateBaseChangeEquiv_tmul k L σ I M N c d l m i

/-- The actual fibre has the same exponent labels over k and L. -/
noncomputable def coordinateGradeBaseChangeIso (q : ℤ) :
    (L ⊗[k] ({i : I // deg i=q} →₀ k)) ≃ₗ[L] ({i : I // deg i=q} →₀ L) :=
  (Finsupp.basisSingleOne.baseChange L).repr

@[simp]
theorem coordinateGradeBaseChangeIso_tmul (q : ℤ) (l : L)
    (a : {i : I // deg i=q} →₀ k) (i : {i : I // deg i=q}) :
    coordinateGradeBaseChangeIso k I deg L q (l ⊗ₜ[k] a) i = algebraMap k L (a i)*l := by
  classical
  simp [coordinateGradeBaseChangeIso,Module.Basis.baseChange_repr_tmul,Algebra.smul_def]

end NSP14.Homological
