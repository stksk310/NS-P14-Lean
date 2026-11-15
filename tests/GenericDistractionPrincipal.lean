module
public import NSP14.Lex.GenericDistractionPrincipal
@[expose] public section
namespace NSP14.Tests.GenericDistractionPrincipal
variable (k : Type) [Field k] (q n : ℕ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_principal_minor (e : ι ↪ Lex.PolynomialDegreeIndex q n) :
    ((Lex.genericFieldDegreeMatrix k q n).submatrix e e).det≠0 :=
  Lex.genericFieldDegreeMatrix_principal_det_ne_zero k q n e
end NSP14.Tests.GenericDistractionPrincipal
