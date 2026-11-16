module
public import NSP14.Homological.ActionOnComplex
public import NSP14.Homological.NativeCoefficientComplex
public import NSP14.Homological.PascalBound
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  (K : ChainComplex (ModuleCat.{u} R) ℕ)
  [∀ i,Module.Finite k ((nativeCoefficientComplex k R K).homology i)]

/-- Finiteness propagates through actual cones using finite homology only. -/
theorem actionOnComplex_coefficient_finite (rs : List R) :
    ∀ i,Module.Finite k ((nativeCoefficientComplex k R ((actionOnComplex R rs).obj K)).homology i) := by
  induction rs with
  | nil => intro i;exact inferInstanceAs (Module.Finite k ((nativeCoefficientComplex k R K).homology i))
  | cons r rs ih =>
    let := ih
    intro i
    exact nativeCoefficientCone_finite k R ((actionOnComplex R rs).obj K) r i

/-- The binomial bound is derived from the genuine cone exact sequences. -/
theorem actionOnComplex_coefficient_bound (rs : List R) : ∀ i,
    Module.finrank k ((nativeCoefficientComplex k R ((actionOnComplex R rs).obj K)).homology i) ≤
      pascalIter (fun j => Module.finrank k ((nativeCoefficientComplex k R K).homology j)) rs.length i := by
  induction rs with
  | nil => intro i;exact le_rfl
  | cons r rs ih =>
    let := actionOnComplex_coefficient_finite k R K rs
    intro i
    have hc := nativeCoefficientCone_bound k R ((actionOnComplex R rs).obj K) r i
    have hstep : Module.finrank k ((nativeCoefficientComplex k R ((actionOnComplex R (r::rs)).obj K)).homology i) ≤
        pascalStep (fun j => Module.finrank k ((nativeCoefficientComplex k R ((actionOnComplex R rs).obj K)).homology j)) i := by
      change Module.finrank k ((nativeCoefficientComplex k R
        ((scalarConeFunctor R r).obj ((actionOnComplex R rs).obj K))).homology i) ≤ _
      cases i with
      | zero => simpa [pascalStep] using hc
      | succ i => simpa [pascalStep] using hc
    exact hstep.trans (pascalStep_mono ih i)
end NSP14.Homological
