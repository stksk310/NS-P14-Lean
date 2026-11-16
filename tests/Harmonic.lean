module
public import NSP14
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
open NSP14.Homological CategoryTheory CategoryTheory.Limits
open scoped BigOperators
namespace HarmonicAcceptance

/-- Specialization to characteristic two preserves the same actual-module
estimate. The proof performs no division inside ZMod 2. -/
theorem characteristic_two (r : ℕ) (M : ModuleCat (VariableRing (ZMod 2) (Fin r)))
    [Module.Finite (VariableRing (ZMod 2) (Fin r)) M]
    [Module.Finite (ZMod 2) (coefficientModule (ZMod 2) (Fin r) M)]
    (G : GradedPolynomialModule (ZMod 2) (Fin r) M) (b : ℤ) (N : ℕ)
    (hgen : Submodule.span (VariableRing (ZMod 2) (Fin r))
      (Set.range (fun a : G.piece b => (show M from G.inclusion b a)))=⊤)
    (hN : ∀ t : ℕ,N < t → IsZero (G.piece (b+t))) (j : ℕ) (hj : 1 ≤ j ∧ j < r) :
    (bettiEuler (ZMod 2) (Fin r) M j : ℚ) ≤ ((r-1).choose j : ℚ)*
      ∑ t ∈ Finset.range (N+1),((j : ℚ)/(t+j))*Module.finrank (ZMod 2) (G.piece (b+t)) :=
  harmonic_bound (ZMod 2) r M G b N hgen hN j hj

end HarmonicAcceptance
