module
public import NSP14.Lex.GenericDistraction
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
noncomputable section
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

abbrev GenericDistractionField := FractionRing (GenericCoefficientRing k q)

def genericFieldLinear (i : Fin q) (n : ℕ) :
    MvPolynomial (Fin q) (GenericDistractionField k q) :=
  MvPolynomial.map (algebraMap _ _) (genericLinearRaw k q i n)

def genericFieldDistraction (a : Fin q →₀ ℕ) :
    MvPolynomial (Fin q) (GenericDistractionField k q) :=
  MvPolynomial.map (algebraMap _ _) (genericRawDistraction k q a)

theorem genericFieldDistraction_eq_product (a : Fin q →₀ ℕ) :
    genericFieldDistraction k q a =
      distractionMonomial (GenericDistractionField k q) q (genericFieldLinear k q) a := by
  simp only [genericFieldDistraction,genericRawDistraction,distractionMonomial,
    genericFieldLinear,map_prod]

theorem genericFieldDistraction_step (a : Fin q →₀ ℕ) (i : Fin q) :
    genericFieldDistraction k q (a+Finsupp.single i 1) =
      genericFieldLinear k q i (a i)*genericFieldDistraction k q a := by
  simp only [genericFieldDistraction_eq_product]
  exact distractionMonomial_step _ _ _ _ _

theorem genericFieldDistraction_homogeneous (a : Fin q →₀ ℕ) :
    (genericFieldDistraction k q a).IsHomogeneous a.degree :=
  (distractionMonomial_homogeneous _ _ _ (genericLinearRaw_homogeneous k q) a).map _

def genericFieldMatrix (a : Fin q →₀ ℕ) :
    Matrix (Fin q) (Fin q) (GenericDistractionField k q) :=
  (genericRawMatrix k q a).map (algebraMap _ _)

theorem genericFieldMatrix_det_ne_zero (a : Fin q →₀ ℕ) :
    (genericFieldMatrix k q a).det ≠ 0 := by
  change ((genericRawMatrix k q a).map (algebraMap _ _)).det ≠ 0
  have he := (algebraMap (GenericCoefficientRing k q) (GenericDistractionField k q)).map_det
    (genericRawMatrix k q a)
  change algebraMap _ _ ((genericRawMatrix k q a).det) =
    ((genericRawMatrix k q a).map (algebraMap _ _)).det at he
  rw [← he]
  exact fun h => genericRawMatrix_det_ne_zero k q a
    ((IsFractionRing.injective (GenericCoefficientRing k q)
      (GenericDistractionField k q)) (h.trans (map_zero _).symm))

def genericFieldLinearEquiv (a : Fin q →₀ ℕ) :
    (Fin q → GenericDistractionField k q) ≃ₗ[GenericDistractionField k q]
      (Fin q → GenericDistractionField k q) :=
  Matrix.toLinearEquiv (Pi.basisFun _ _) (genericFieldMatrix k q a)
    (isUnit_iff_ne_zero.mpr (genericFieldMatrix_det_ne_zero k q a))

def genericFieldDegreeMatrix (n : ℕ) :
    Matrix (PolynomialDegreeIndex q n) (PolynomialDegreeIndex q n)
      (GenericDistractionField k q) :=
  (genericRawDegreeMatrix k q n).map (algebraMap _ _)

theorem genericFieldDegreeMatrix_entry (n : ℕ) (r s : PolynomialDegreeIndex q n) :
    genericFieldDegreeMatrix k q n r s = (genericFieldDistraction k q s.val).coeff r.val := by
  simp only [genericFieldDegreeMatrix,Matrix.map_apply,genericRawDegreeMatrix,
    genericFieldDistraction,MvPolynomial.coeff_map]

theorem genericFieldDegreeMatrix_det_ne_zero (n : ℕ) :
    (genericFieldDegreeMatrix k q n).det ≠ 0 := by
  change ((genericRawDegreeMatrix k q n).map (algebraMap _ _)).det ≠ 0
  have he := (algebraMap (GenericCoefficientRing k q) (GenericDistractionField k q)).map_det
    (genericRawDegreeMatrix k q n)
  change algebraMap _ _ ((genericRawDegreeMatrix k q n).det) =
    ((genericRawDegreeMatrix k q n).map (algebraMap _ _)).det at he
  rw [← he]
  exact fun h => genericRawDegreeMatrix_det_ne_zero k q n
    ((IsFractionRing.injective (GenericCoefficientRing k q)
      (GenericDistractionField k q)) (h.trans (map_zero _).symm))

def genericFieldDegreeEquiv (n : ℕ) :
    (PolynomialDegreeIndex q n → GenericDistractionField k q) ≃ₗ[GenericDistractionField k q]
      (PolynomialDegreeIndex q n → GenericDistractionField k q) :=
  Matrix.toLinearEquiv (Pi.basisFun _ _) (genericFieldDegreeMatrix k q n)
    (isUnit_iff_ne_zero.mpr (genericFieldDegreeMatrix_det_ne_zero k q n))
end NSP14.Lex
