module
public import NSP14.Lex.GenericDistractionStep
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.GenericDistractionStep
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => Lex.GenericDistractionField k q

theorem actual_homogeneous_step (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (i : ℕ) (t : ℤ) :
    Lex.quotientGradedBetti k q I hI i t ≤
      Lex.quotientGradedBetti K q
        (Lex.initialIdeal K q MonomialOrder.degLex
          (Lex.genericDistractionIdeal k q
            (Lex.monomialExtension k K q (Lex.initialIdeal k q MonomialOrder.degLex I))))
        (Lex.initialIdeal_homogeneous K q MonomialOrder.degLex
          (Lex.genericDistractionIdeal k q
            (Lex.monomialExtension k K q (Lex.initialIdeal k q MonomialOrder.degLex I)))) i t :=
  Lex.genericHomogeneousStep_gradedBetti_le k q I hI i t
end NSP14.Tests.GenericDistractionStep
