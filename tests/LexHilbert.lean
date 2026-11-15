module
public import NSP14.Lex.LexExistence
@[expose] public section
namespace NSP14.Tests.LexHilbert
variable (k : Type) [Field k] (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem one_actual_lex_whole_Hilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) :
    ∃ (L : Ideal (MvPolynomial (Fin q) k)) (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)),
      Lex.IsLex k q L ∧ ∀ n,Lex.quotientHilbert k q I hI n=Lex.quotientHilbert k q L hL n :=
  Lex.exists_lex_sameHilbert k q I hI
end NSP14.Tests.LexHilbert
