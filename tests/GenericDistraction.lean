module
public import NSP14.Lex.GenericDistraction
@[expose] public section
open scoped Classical
namespace NSP14.Tests.GenericDistraction
theorem actual_generic_linear_determinant (k : Type) [CommRing k] [Nontrivial k] (q : ℕ)
    (a : Fin q →₀ ℕ) :
    (show Matrix (Fin q) (Fin q) (MvPolynomial (Fin q × ℕ × Fin q) k) from
      fun r i => MvPolynomial.X (i,a i,r)).det ≠ 0 :=
  Lex.genericRawMatrix_det_ne_zero k q a

theorem actual_generic_degree_determinant (k : Type) [CommRing k] [Nontrivial k] (q n : ℕ) :
    (Lex.genericRawDegreeMatrix k q n).det ≠ 0 := Lex.genericRawDegreeMatrix_det_ne_zero k q n
end NSP14.Tests.GenericDistraction
