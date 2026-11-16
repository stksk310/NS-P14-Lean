module

public import NSP14.Homological.ActualGradedBaseChange
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.CharP.Algebra

@[expose] public section

namespace NSP14.Homological

variable (k : Type) [Field k]

/-- A fixed infinite pure transcendental extension, also for finite k. -/
abbrev InfiniteScalarField := RatFunc k

noncomputable instance infiniteScalarFieldInfinite : Infinite (InfiniteScalarField k) := by
  have hp : Function.Injective (fun n : ℕ => (Polynomial.X : Polynomial k) ^ n) := by
    intro i j h
    have he := congrArg Polynomial.natDegree h
    simpa using he
  exact Infinite.of_injective
    (fun n : ℕ => algebraMap (Polynomial k) (RatFunc k) (Polynomial.X ^ n))
    ((IsFractionRing.injective (Polynomial k) (RatFunc k)).comp hp)

/-- Same characteristic, supplied explicitly rather than inferred from cardinality. -/
theorem infiniteScalarField_charP (p : ℕ) [CharP k p] : CharP (InfiniteScalarField k) p :=
  charP_of_injective_algebraMap (algebraMap k (RatFunc k)).injective p

end NSP14.Homological
