module
public import NSP14.Lex.LexTailCorrection
@[expose] public section
namespace NSP14.Tests.LexTailCorrection
variable (k : Type) [Field k] (s r N : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem actual_same_K (I : Ideal (MvPolynomial (Fin (s+r)) k)) (hI : Lex.IsLex k (s+r) I)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (s+r)) k))
    (h2 : Lex.quotientHilbert k (s+r) I hHom 2≤Fintype.card (Lex.PolynomialDegreeIndex r 2)) :
    Lex.lexCorrection k r (Lex.suffixVariableIdeal k s r I) N=Lex.lexCorrection k (s+r) I N :=
  Lex.IsLex.suffix_sameCorrection k s r I hI hHom h2 N
end NSP14.Tests.LexTailCorrection
