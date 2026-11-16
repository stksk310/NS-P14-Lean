module
public import NSP14.Lex.GenericDistractionField
public import Mathlib.RingTheory.Localization.FractionRing
@[expose] public section
open scoped Classical
namespace NSP14.Tests.GenericDistractionField
theorem actual_generic_matrix_over_field (k : Type) [Field k] (q : ℕ) (a : Fin q →₀ ℕ) :
    ((Lex.genericRawMatrix k q a).map
      (algebraMap (Lex.GenericCoefficientRing k q)
        (FractionRing (Lex.GenericCoefficientRing k q)))).det ≠ 0 :=
  Lex.genericFieldMatrix_det_ne_zero k q a

theorem actual_generic_degree_over_field (k : Type) [Field k] (q n : ℕ) :
    ((Lex.genericRawDegreeMatrix k q n).map
      (algebraMap (Lex.GenericCoefficientRing k q)
        (FractionRing (Lex.GenericCoefficientRing k q)))).det ≠ 0 :=
  Lex.genericFieldDegreeMatrix_det_ne_zero k q n
end NSP14.Tests.GenericDistractionField
