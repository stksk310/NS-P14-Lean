module
public import NSP14.Lex.GenericDistractionField
public import Mathlib.RingTheory.MvPolynomial.Basic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators Matrix
noncomputable section
namespace NSP14.Lex
variable (k : Type) [Field k] (q n : ℕ)
def degreeMonomialBasis : Module.Basis (PolynomialDegreeIndex q n) k
    (MvPolynomial.homogeneousSubmodule (Fin q) k n) :=
  (MvPolynomial.basisRestrictSupport k {a : Fin q →₀ ℕ | a.degree=n}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (Fin q) k n).symm)
theorem degreeMonomialBasis_apply (a : PolynomialDegreeIndex q n) :
    ((degreeMonomialBasis k q n a : MvPolynomial.homogeneousSubmodule (Fin q) k n) : MvPolynomial (Fin q) k)=
      MvPolynomial.monomial a.val 1 := by
  have he : degreeMonomialBasis k q n a =
      ⟨MvPolynomial.monomial a.val 1, MvPolynomial.isHomogeneous_monomial 1 a.property⟩ := by
    apply (degreeMonomialBasis k q n).repr.injective
    ext r
    rw [Module.Basis.repr_self]
    change Finsupp.single a (1:k) r = (MvPolynomial.monomial a.val (1:k)).coeff r.val
    simp only [Finsupp.single_apply,MvPolynomial.coeff_monomial]
    congr 1
    exact propext Subtype.ext_iff
  exact congrArg Subtype.val he
theorem degreeMonomialBasis_repr (f : MvPolynomial.homogeneousSubmodule (Fin q) k n) (a : PolynomialDegreeIndex q n) :
    (degreeMonomialBasis k q n).repr f a = f.val.coeff a.val := by
  rfl

def genericFieldPieceEquiv :
    (MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q) n) ≃ₗ[GenericDistractionField k q]
      (MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q) n) :=
  Matrix.toLinearEquiv (degreeMonomialBasis (GenericDistractionField k q) q n)
    (genericFieldDegreeMatrix k q n)
    (isUnit_iff_ne_zero.mpr (genericFieldDegreeMatrix_det_ne_zero k q n))

theorem genericFieldPieceEquiv_basis (a : PolynomialDegreeIndex q n) :
    genericFieldPieceEquiv k q n (degreeMonomialBasis (GenericDistractionField k q) q n a)=
      ⟨genericFieldDistraction k q a.val, by
        rw [MvPolynomial.mem_homogeneousSubmodule]
        simpa only [a.property] using genericFieldDistraction_homogeneous k q a.val⟩ := by
  apply (degreeMonomialBasis (GenericDistractionField k q) q n).repr.injective
  ext r
  unfold genericFieldPieceEquiv
  rw [Matrix.toLinearEquiv_apply,Matrix.repr_toLin,Module.Basis.repr_self]
  change (genericFieldDegreeMatrix k q n *ᵥ Finsupp.single a 1) r =
    (genericFieldDistraction k q a.val).coeff r.val
  simpa [Matrix.mulVec,dotProduct,Finsupp.single_apply] using
    genericFieldDegreeMatrix_entry k q n r a

local instance : DirectSum.Decomposition
    (MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q)) :=
  MvPolynomial.decomposition

/-- The actual distraction on every monomial, assembled as a field-linear equivalence. -/
def genericPolynomialEquiv : MvPolynomial (Fin q) (GenericDistractionField k q) ≃ₗ[GenericDistractionField k q]
    MvPolynomial (Fin q) (GenericDistractionField k q) :=
  (DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q))).trans
    ((DirectSum.congrLinearEquiv (genericFieldPieceEquiv k q)).trans
      (DirectSum.decomposeLinearEquiv (MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q))).symm)

theorem genericPolynomialEquiv_monomial (a : Fin q →₀ ℕ) :
    genericPolynomialEquiv k q (MvPolynomial.monomial a 1)=genericFieldDistraction k q a := by
  let b := degreeMonomialBasis (GenericDistractionField k q) q a.degree
  let v := b ⟨a,rfl⟩
  have hv : (v : MvPolynomial (Fin q) (GenericDistractionField k q))=MvPolynomial.monomial a 1 :=
    degreeMonomialBasis_apply _ _ _ _
  rw [← hv]
  unfold genericPolynomialEquiv
  rw [LinearEquiv.trans_apply,DirectSum.decomposeLinearEquiv_apply_coe,
    LinearEquiv.trans_apply,DirectSum.coe_congrLinearEquiv,DirectSum.lmap_lof,
    DirectSum.decomposeLinearEquiv_symm_lof]
  exact congrArg Subtype.val (genericFieldPieceEquiv_basis k q a.degree ⟨a,rfl⟩)

/-- The whole polynomial equivalence restricts to the actual equivalence in each degree. -/
theorem genericPolynomialEquiv_piece
    (f : MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q) n) :
    genericPolynomialEquiv k q f.val=(genericFieldPieceEquiv k q n f).val := by
  unfold genericPolynomialEquiv
  rw [LinearEquiv.trans_apply,DirectSum.decomposeLinearEquiv_apply_coe,
    LinearEquiv.trans_apply,DirectSum.coe_congrLinearEquiv,DirectSum.lmap_lof,
    DirectSum.decomposeLinearEquiv_symm_lof]
  rfl

/-- Homogeneity is preserved in both directions, over the genuine generic coefficient field. -/
theorem genericPolynomialEquiv_homogeneous_iff
    (f : MvPolynomial (Fin q) (GenericDistractionField k q)) :
    (genericPolynomialEquiv k q f).IsHomogeneous n ↔ f.IsHomogeneous n := by
  constructor
  · intro hf
    let v : MvPolynomial.homogeneousSubmodule (Fin q) (GenericDistractionField k q) n :=
      ⟨genericPolynomialEquiv k q f,hf⟩
    let w := (genericFieldPieceEquiv k q n).symm v
    have hw : genericPolynomialEquiv k q w.val=genericPolynomialEquiv k q f := by
      rw [genericPolynomialEquiv_piece]
      exact congrArg Subtype.val ((genericFieldPieceEquiv k q n).apply_symm_apply v)
    have he : w.val=f := (genericPolynomialEquiv k q).injective hw
    rw [← he]
    exact w.property
  · intro hf
    rw [show genericPolynomialEquiv k q f=
      (genericFieldPieceEquiv k q n ⟨f,hf⟩).val from genericPolynomialEquiv_piece k q n ⟨f,hf⟩]
    exact (genericFieldPieceEquiv k q n ⟨f,hf⟩).property
end NSP14.Lex
