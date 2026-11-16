module
public import NSP14.Lex.StrongStableRestriction
@[expose] public section
open scoped Classical
namespace NSP14.Tests.StrongStableRestriction
variable (k : Type) [Field k] (q d : ℕ)

theorem actual_last_variable_restriction
    (I L : Ideal (MvPolynomial (Fin (q+2)) k)) (hI : Lex.IsStronglyStable k (q+2) I)
    (hL : Lex.IsLex k (q+2) L)
    (hcard : Fintype.card {α : Lex.PolynomialDegreeIndex (q+2) d // MvPolynomial.monomial α.val (1:k)∈L}≤
      Fintype.card {α : Lex.PolynomialDegreeIndex (q+2) d // MvPolynomial.monomial α.val (1:k)∈I}) :
    (Finset.univ.filter (fun α : Lex.PolynomialDegreeIndex (q+2) d =>
      MvPolynomial.monomial α.val (1:k)∈L ∧ α.val (Fin.last (q+1))=0)).card≤
    (Finset.univ.filter (fun α : Lex.PolynomialDegreeIndex (q+2) d =>
      MvPolynomial.monomial α.val (1:k)∈I ∧ α.val (Fin.last (q+1))=0)).card :=
  Lex.IsStronglyStable.last_zero_count_le k q d I L hI hL hcard
end NSP14.Tests.StrongStableRestriction
