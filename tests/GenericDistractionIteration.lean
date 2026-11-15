module
public import NSP14.Lex.GenericDistractionIteration
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Tests.GenericDistractionIteration
variable (k : Type) [Field k] (q : ℕ)

theorem actual_strongly_stable_extension (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) :
    ∃ (L : Type) (fieldL : Field L),
      letI : Field L := fieldL
      ∃ (_ : Algebra k L) (J : Ideal (MvPolynomial (Fin q) L))
        (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) L)),
        Lex.IsMonomial L q J ∧
        (∀ v,MvPolynomial.monomial v (1:L)∈J →
          ∀ a b,0<v b → a<b → MvPolynomial.monomial (Lex.raisedExponent q v a b) (1:L)∈J) ∧
        (∀ n,Lex.quotientHilbert k q I hI n=Lex.quotientHilbert L q J hJ n) ∧
        (∀ i t,Lex.quotientGradedBetti k q I hI i t≤Lex.quotientGradedBetti L q J hJ i t) :=
  Lex.exists_stronglyStable_comparison k q I hI
end NSP14.Tests.GenericDistractionIteration
