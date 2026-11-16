module
public import NSP14.Homological.StandardHarmonic
public import NSP14.Homological.GeneratedDegreePresentation
public import NSP14.Homological.FiniteDegreeSum
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped Classical BigOperators
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ] [Nonempty σ]
  (M : ModuleCat.{u} (VariableRing k σ))
  [Module.Finite (VariableRing k σ) M] [Module.Finite k (coefficientModule k σ M)]
  (G : GradedPolynomialModule k σ M)

/-- Actual finite-length generated-in-one-degree harmonic estimate. The
standard module, its basis, the differential minor and averaging are all
constructed; no rank estimate or dimension-preservation input is assumed. -/
theorem generated_harmonic_bound (m : MonomialOrder σ) (b : ℤ) (N : ℕ)
    (hgen : Submodule.span (VariableRing k σ)
      (Set.range (fun a : G.piece b => (show M from G.inclusion b a)))=⊤)
    (hN : ∀ t : ℕ,N < t → IsZero (G.piece (b+t))) (j : ℕ) (hj : 0 < j) :
    (bettiEuler k σ M j : ℚ) ≤ ((Fintype.card σ-1).choose j : ℚ)*
      ∑ t ∈ Finset.range (N+1),((j : ℚ)/(t+j))*Module.finrank k (G.piece (b+t)) := by
  let g := degreeGenerators k σ M G b
  have hg : Submodule.span (VariableRing k σ) (Set.range g)=⊤ :=
    degreeGenerators_polynomial_span k σ M G b hgen
  have hdg : ∀ i,g i ∈ G.degreeSpace b := degreeGenerators_homogeneous k σ M G b
  let : Finite (ModuleStandard k m g) := moduleStandard_finite k m g hg
  let : Fintype (ModuleStandard k m g) := Fintype.ofFinite _
  let d : ModuleStandard k m g → ℕ := fun i => (moduleTermExponent m i.val).degree
  have hc (t : ℕ) : Module.finrank k (G.piece (b+t))=
      Nat.card {i : ModuleStandard k m g // d i=t} := by
    simpa only [d,moduleTermExponent,add_right_inj,Nat.cast_inj] using
      moduleStandardBasis_degree_count k σ M G m g b hg hdg t
  have hs (i : ModuleStandard k m g) : d i ≤ N := by
    by_contra hle
    have hz := hN (d i) (Nat.lt_of_not_ge hle)
    let : Subsingleton (G.piece (b+d i)) := ModuleCat.subsingleton_of_isZero hz
    have hf : Module.finrank k (G.piece (b+d i))=0 := Module.finrank_zero_of_subsingleton
    rw [hc] at hf
    have hpos : 0 < Nat.card {i' : ModuleStandard k m g // d i'=d i} := by
      let : Nonempty {i' : ModuleStandard k m g // d i'=d i} := ⟨⟨i,rfl⟩⟩
      exact Nat.card_pos
    omega
  have h := standard_harmonic_bound k σ M m g hg j hj
  change (bettiEuler k σ M j : ℚ) ≤ ((Fintype.card σ-1).choose j : ℚ)*
    ∑ i : ModuleStandard k m g,(j : ℚ)/(d i+j) at h
  rw [finite_degree_sum d N hs (fun t => (j : ℚ)/(t+j))] at h
  simpa only [← hc] using h

end NSP14.Homological
namespace NSP14.Homological

/-- Fin r export matching the original Run15 harmonic obligation. -/
theorem harmonic_bound (k : Type) [Field k] (r : ℕ) (M : ModuleCat (VariableRing k (Fin r)))
    [Module.Finite (VariableRing k (Fin r)) M]
    [Module.Finite k (coefficientModule k (Fin r) M)]
    (G : GradedPolynomialModule k (Fin r) M) (b : ℤ) (N : ℕ)
    (hgen : Submodule.span (VariableRing k (Fin r))
      (Set.range (fun a : G.piece b => (show M from G.inclusion b a)))=⊤)
    (hN : ∀ t : ℕ,N < t → IsZero (G.piece (b+t))) (j : ℕ) (hj : 1 ≤ j ∧ j < r) :
    (bettiEuler k (Fin r) M j : ℚ) ≤ ((r-1).choose j : ℚ)*
      ∑ t ∈ Finset.range (N+1),((j : ℚ)/(t+j))*Module.finrank k (G.piece (b+t)) := by
  let : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp (by omega)
  simpa only [Fintype.card_fin] using
    generated_harmonic_bound k (Fin r) M G MonomialOrder.degLex b N hgen hN j (by omega)
end NSP14.Homological
