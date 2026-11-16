module
public import NSP14.Lex.DistractionGraded
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.DistractionGraded
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => Lex.GenericDistractionField k q

theorem actual_all_graded_betti_numbers (I : Ideal (MvPolynomial (Fin q) K))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) K))
    (hmono : Lex.IsMonomial K q I) (i : ℕ) (t : ℤ) :
    Lex.quotientGradedBetti K q I hI i t =
      Lex.quotientGradedBetti K q (Lex.genericDistractionIdeal k q I)
        (Lex.genericDistractionIdeal_homogeneous k q I) i t :=
  Lex.genericDistraction_gradedBetti k q I hI hmono i t
end NSP14.Tests.DistractionGraded
