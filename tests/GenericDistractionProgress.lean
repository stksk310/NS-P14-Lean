module
public import NSP14.Lex.GenericDistractionProgress
@[expose] public section
open scoped Classical
namespace NSP14.Tests.GenericDistractionProgress
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => Lex.GenericDistractionField k q

theorem actual_prefix_does_not_decrease (I : Ideal (MvPolynomial (Fin q) k))
    (n : ℕ) (v : Lex.PolynomialDegreeIndex q n) :
    Fintype.card {a : Lex.PolynomialDegreeIndex q n //
      MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn a.val ∧
        MvPolynomial.monomial a.val (1:k)∈I}≤
    Fintype.card {a : Lex.PolynomialDegreeIndex q n //
      MonomialOrder.degLex.toSyn v.val≤MonomialOrder.degLex.toSyn a.val ∧
        MvPolynomial.monomial a.val (1:K)∈Lex.genericMonomialStep k q I} :=
  Lex.genericMonomialStep_prefixCard_le k q I n v
end NSP14.Tests.GenericDistractionProgress
