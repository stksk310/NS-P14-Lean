module
public import NSP14.Lex.DegreeSeparator
@[expose] public section
namespace NSP14.Tests.DegreeSeparator

theorem actual_degree_card (q d : ℕ) :
    Fintype.card (Lex.PolynomialDegreeIndex (q+1) d)=(d+q).choose q :=
  Lex.degreeIndex_card_choose q d
#check @Lex.degreeSeparatorEquiv
#check @Lex.degreeSeparator_colex_lt_iff
end NSP14.Tests.DegreeSeparator
