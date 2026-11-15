module
public import NSP14.Lex.DegreeFamily
@[expose] public section
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.DegreeFamily
variable (k : Type) [Field k] (q d : ℕ)

theorem actual_monomial_count_and_hilbert (I : Ideal (MvPolynomial (Fin (q+1)) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (q+1)) k))
    (hmono : Lex.IsMonomial k (q+1) I) :
    Fintype.card {α : Lex.PolynomialDegreeIndex (q+1) d // MvPolynomial.monomial α.val (1:k)∈I}+
      Lex.quotientHilbert k (q+1) I hI d=Fintype.card (Lex.PolynomialDegreeIndex (q+1) d) :=
  Lex.monomialDegreeCard_add_hilbert k q d I hI hmono
end NSP14.Tests.DegreeFamily
