module
public import NSP14.Lex.LexTailSupport
@[expose] public section
namespace NSP14.Tests.LexTailSupport
variable (k : Type) [Field k] (s r : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem actual_high_standard_tail (I : Ideal (MvPolynomial (Fin (s+r)) k)) (hI : Lex.IsLex k (s+r) I)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (s+r)) k))
    (h2 : Lex.quotientHilbert k (s+r) I hHom 2≤Fintype.card (Lex.PolynomialDegreeIndex r 2))
    (α : Fin (s+r) →₀ ℕ) (hd : 2≤α.degree) (ha : MvPolynomial.monomial α (1:k)∉I) :
    ∀ j,j.val<s → α j=0 := Lex.IsLex.standard_tail_support k s r I hI hHom h2 α hd ha
end NSP14.Tests.LexTailSupport
