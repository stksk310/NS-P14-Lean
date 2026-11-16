module
public import NSP14
@[expose] public section
namespace SemigroupAlgebraPresentationAcceptance
open NSP14
variable (S : NumericalSemigroup) (k : Type) [Field k]
theorem actual_full_atoms : Function.Surjective (S.fullPolynomialToSemigroupRing k) :=
  S.fullPolynomialToSemigroupRing_surjective k
end SemigroupAlgebraPresentationAcceptance
