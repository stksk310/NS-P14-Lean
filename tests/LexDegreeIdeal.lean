module
public import NSP14.Lex.LexDegreeIdeal
@[expose] public section
namespace NSP14.Tests.LexDegreeIdeal
variable (k : Type) [Field k] (q d : ℕ)
theorem actual_generated_lex (S : Finset (Lex.PolynomialDegreeIndex q d))
    (hu : ∀ a∈S,∀ b : Lex.PolynomialDegreeIndex q d,MonomialOrder.lex.toSyn a.val≤MonomialOrder.lex.toSyn b.val → b∈S) :
    Lex.IsLex k q (Lex.degreeGeneratedIdeal k q d S) := Lex.degreeGeneratedIdeal_isLex k q d S hu
end NSP14.Tests.LexDegreeIdeal
