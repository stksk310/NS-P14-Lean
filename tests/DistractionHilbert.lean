module
public import NSP14.Lex.DistractionHilbert
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.DistractionHilbert
theorem actual_whole_hilbert_function (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) (Lex.GenericDistractionField k q)))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) (Lex.GenericDistractionField k q)))
    (hmono : Lex.IsMonomial (Lex.GenericDistractionField k q) q I) :
    ∀ n, Lex.quotientHilbert (Lex.GenericDistractionField k q) q I hI n =
      Lex.quotientHilbert (Lex.GenericDistractionField k q) q (Lex.genericDistractionIdeal k q I)
        (Lex.genericDistractionIdeal_homogeneous k q I) n :=
  Lex.genericDistraction_sameHilbert k q I hI hmono
end NSP14.Tests.DistractionHilbert
