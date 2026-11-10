module
public import NSP14.Homological.ActionComplexBound
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  (K : ChainComplex (ModuleCat.{u} R) ℕ)
  [∀ i,Module.Finite k ((nativeCoefficientComplex k R K).homology i)]

/-- Real truncation, exact cones and their homology bounds retain the
H0 correction. No chain group is required to be finite-dimensional. -/
theorem correctedActionComparison (rs : List R)
    (h0finite : ∀ i,Module.Finite k ((nativeCoefficientComplex k R
      ((actionOnComplex R rs).obj ((ChainComplex.single₀ _).obj (K.homology 0)))).homology i)) (i : ℕ) :
    Module.finrank k ((nativeCoefficientComplex k R ((actionOnComplex R rs).obj K)).homology i) ≤
      Module.finrank k ((nativeCoefficientComplex k R
        ((actionOnComplex R rs).obj ((ChainComplex.single₀ _).obj (K.homology 0)))).homology i)+
      binomialTransform rs.length (fun j => if j=0 then 0 else
        Module.finrank k ((nativeCoefficientComplex k R K).homology j)) i := by
  let : ∀ j,Module.Finite k ((nativeCoefficientComplex k R (h0KernelSequence R K).X₁).homology j) :=
    coefficientH0Kernel_finite k R K
  let := actionOnComplex_coefficient_finite k R (h0KernelSequence R K).X₁ rs
  let := h0finite
  have hs := actionOnComplex_shortExact R rs (h0KernelSequence R K) (h0KernelSequence_shortExact R K)
  have hsc := nativeCoefficient_shortExact k R _ hs
  let : Module.Finite k ((((h0KernelSequence R K).map (actionOnComplex R rs)).map
      (nativeCoefficientFunctor k R)).X₁.homology i) :=
    actionOnComplex_coefficient_finite k R (h0KernelSequence R K).X₁ rs i
  let : Module.Finite k ((((h0KernelSequence R K).map (actionOnComplex R rs)).map
      (nativeCoefficientFunctor k R)).X₃.homology i) := h0finite i
  have hb := homology_finrank_bound k _ hsc i
  change Module.finrank k ((nativeCoefficientComplex k R ((actionOnComplex R rs).obj K)).homology i) ≤
      Module.finrank k ((nativeCoefficientComplex k R ((actionOnComplex R rs).obj (h0KernelSequence R K).X₁)).homology i)+
      Module.finrank k ((nativeCoefficientComplex k R
        ((actionOnComplex R rs).obj ((ChainComplex.single₀ _).obj (K.homology 0)))).homology i) at hb
  have hc := actionOnComplex_coefficient_bound k R (h0KernelSequence R K).X₁ rs i
  have he : (fun j => Module.finrank k ((nativeCoefficientComplex k R (h0KernelSequence R K).X₁).homology j))=
      (fun j => if j=0 then 0 else Module.finrank k ((nativeCoefficientComplex k R K).homology j)) := by
    funext j
    cases j with
    | zero =>
      have : Subsingleton ((nativeCoefficientComplex k R (h0KernelSequence R K).X₁).homology 0) :=
        ModuleCat.subsingleton_of_isZero (coefficientH0KernelZero k R K)
      simp only [ite_true,Module.finrank_zero_of_subsingleton]
    | succ j =>
      simpa only [Nat.succ_ne_zero,ite_false] using (coefficientH0KernelPositiveIso k R K j).toLinearEquiv.finrank_eq
  rw [pascalIter_eq_binomialTransform,he] at hc
  omega
end NSP14.Homological
