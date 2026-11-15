module
public import NSP14.Lex.GenericDistractionField
@[expose] public section
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q n : ℕ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem genericRawDegreeMatrix_principal_specialize (e : ι ↪ PolynomialDegreeIndex q n) :
    ((genericRawDegreeMatrix k q n).submatrix e e).map (diagonalParameterMap k q)=1 := by
  rw [← Matrix.submatrix_map,genericRawDegreeMatrix_specialize,Matrix.submatrix_one_embedding]

theorem genericRawDegreeMatrix_principal_det_ne_zero (e : ι ↪ PolynomialDegreeIndex q n) :
    ((genericRawDegreeMatrix k q n).submatrix e e).det≠0 := by
  have hd : diagonalParameterMap k q (((genericRawDegreeMatrix k q n).submatrix e e).det)=1 := by
    rw [(diagonalParameterMap k q).map_det]
    change (((genericRawDegreeMatrix k q n).submatrix e e).map (diagonalParameterMap k q)).det=1
    rw [genericRawDegreeMatrix_principal_specialize,Matrix.det_one]
  intro he
  rw [he,map_zero] at hd
  exact zero_ne_one hd

theorem genericFieldDegreeMatrix_principal_det_ne_zero (e : ι ↪ PolynomialDegreeIndex q n) :
    ((genericFieldDegreeMatrix k q n).submatrix e e).det≠0 := by
  change (((genericRawDegreeMatrix k q n).map (algebraMap _ _)).submatrix e e).det≠0
  rw [Matrix.submatrix_map]
  have he := (algebraMap (GenericCoefficientRing k q) (GenericDistractionField k q)).map_det
    ((genericRawDegreeMatrix k q n).submatrix e e)
  change algebraMap _ _ (((genericRawDegreeMatrix k q n).submatrix e e).det)=
    (((genericRawDegreeMatrix k q n).submatrix e e).map (algebraMap _ _)).det at he
  rw [← he]
  exact fun h => genericRawDegreeMatrix_principal_det_ne_zero k q n e
    ((IsFractionRing.injective (GenericCoefficientRing k q)
      (GenericDistractionField k q)) (h.trans (map_zero _).symm))

def genericPrincipalDegreeEquiv (e : ι ↪ PolynomialDegreeIndex q n) :
    (ι → GenericDistractionField k q) ≃ₗ[GenericDistractionField k q]
      (ι → GenericDistractionField k q) :=
  Matrix.toLinearEquiv (Pi.basisFun _ _) ((genericFieldDegreeMatrix k q n).submatrix e e)
    (isUnit_iff_ne_zero.mpr (genericFieldDegreeMatrix_principal_det_ne_zero k q n e))
end NSP14.Lex
