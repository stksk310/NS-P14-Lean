module
public import NSP14.Homological.RegularActionCoefficient
public import NSP14.Homological.CorrectedActionComparison
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k R σ : Type u) [Field k] [CommRing R] [Algebra k R]
  (rs : List R) (φ : VariableRing k σ →ₐ[k] R) (xs : List σ)
  [∀ i,Module.Finite k ((regularPartialCoefficientComplex k R rs).homology i)]

theorem regularCorrectedComparison
    (h0finite : ∀ i,Module.Finite k ((actionH0SingleCoefficientComplex k R σ rs φ xs).homology i)) (i : ℕ) :
    Module.finrank k ((regularExtendedCoefficientComplex k R σ rs φ xs).homology i) ≤
      Module.finrank k ((actionH0SingleCoefficientComplex k R σ rs φ xs).homology i)+
        binomialTransform xs.length (fun j => if j=0 then 0 else
          Module.finrank k ((regularPartialCoefficientComplex k R rs).homology j)) i := by
  let : ∀ j,Module.Finite k ((nativeCoefficientComplex k R (actionRegularComplex R rs)).homology j) :=
    fun j => inferInstanceAs (Module.Finite k ((regularPartialCoefficientComplex k R rs).homology j))
  have h := correctedActionComparison k R (actionRegularComplex R rs)
    (xs.map (fun x => φ (MvPolynomial.X x))) h0finite i
  simpa only [List.length_map,regularExtendedCoefficientComplex,actionH0SingleCoefficientComplex,regularPartialCoefficientComplex] using h
end NSP14.Homological
