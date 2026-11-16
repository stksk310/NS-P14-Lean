module
public import NSP14.Lex.Stable
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Data.Finsupp.PWO
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem IsMonomial.span {I : Ideal (MvPolynomial (Fin q) k)} (hI : IsMonomial k q I) :
    I=Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
      {v | MvPolynomial.monomial v (1:k)∈I}) := by
  apply le_antisymm
  · intro f hf
    rw [f.as_sum]
    apply Ideal.sum_mem
    intro v hv
    have hm := Ideal.subset_span (s:=((fun v => MvPolynomial.monomial v (1:k)) ''
      {v | MvPolynomial.monomial v (1:k)∈I})) ⟨v,hI f hf v hv,rfl⟩
    have hs := (Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
      {v | MvPolynomial.monomial v (1:k)∈I})).restrictScalars k |>.smul_mem (f.coeff v) hm
    change f.coeff v • MvPolynomial.monomial v (1:k) ∈ Ideal.span _ at hs
    rw [MvPolynomial.smul_monomial,smul_eq_mul,mul_one] at hs
    exact hs
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    exact hv

theorem exponent_degree_strict {v w : Fin q →₀ ℕ} (hle : v ≤ w) (hne : v≠w) : v.degree<w.degree := by
  have hex : ∃ i : Fin q,v i<w i := by
    by_contra! hn
    apply hne
    ext i
    have h0 := hle i
    have h1 := hn i
    omega
  rw [Finsupp.degree_eq_sum,Finsupp.degree_eq_sum]
  apply Finset.sum_lt_sum
  · intro i _
    exact hle i
  · obtain ⟨i,hi⟩ := hex
    exact ⟨i,Finset.mem_univ _,hi⟩

theorem minimal_divisor (I : Ideal (MvPolynomial (Fin q) k)) (v : Fin q →₀ ℕ)
    (hv : MvPolynomial.monomial v (1:k)∈I) :
    ∃ w : Fin q →₀ ℕ,w ≤ v ∧ MinimalGenerator k q I w := by
  have hex : ∃ n : ℕ,∃ w : Fin q →₀ ℕ,w ≤ v ∧ MvPolynomial.monomial w (1:k)∈I ∧ w.degree=n :=
    ⟨v.degree,v,le_rfl,hv,rfl⟩
  obtain ⟨w,hw,hmem,hd⟩ := Nat.find_spec hex
  refine ⟨w,hw,hmem,?_⟩
  intro z hzw hz
  by_contra hne
  have hlt := exponent_degree_strict q hzw hne
  have hmin := Nat.find_min' hex ⟨z,hzw.trans hw,hz,rfl⟩
  omega

theorem monomial_mem_iff_minimal_divisor (I : Ideal (MvPolynomial (Fin q) k)) (v : Fin q →₀ ℕ) :
    MvPolynomial.monomial v (1:k)∈I ↔ ∃ w : Fin q →₀ ℕ,w ≤ v ∧ MinimalGenerator k q I w := by
  constructor
  · exact minimal_divisor k q I v
  · rintro ⟨w,hw,hmin⟩
    have hdvd : MvPolynomial.monomial w (1:k)∣MvPolynomial.monomial v (1:k) :=
      (MvPolynomial.monomial_dvd_monomial (r:=(1:k)) (s:=(1:k))).mpr ⟨Or.inr hw,dvd_rfl⟩
    obtain ⟨g,hg⟩ := hdvd
    rw [hg]
    exact I.mul_mem_right g hmin.1

theorem finite_minimalGenerators (I : Ideal (MvPolynomial (Fin q) k)) :
    {v : Fin q →₀ ℕ | MinimalGenerator k q I v}.Finite := by
  apply WellQuasiOrderedLE.finite_of_isAntichain
  intro v hv w hw hne hle
  exact hne (hw.2 v hle hv.1)

noncomputable def minimalGeneratorFinset (I : Ideal (MvPolynomial (Fin q) k)) : Finset (Fin q →₀ ℕ) :=
  (finite_minimalGenerators k q I).toFinset

theorem mem_minimalGeneratorFinset (I : Ideal (MvPolynomial (Fin q) k)) (v : Fin q →₀ ℕ) :
    v∈minimalGeneratorFinset k q I ↔ MinimalGenerator k q I v := by
  simp only [minimalGeneratorFinset,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]

theorem IsMonomial.span_minimal {I : Ideal (MvPolynomial (Fin q) k)} (hI : IsMonomial k q I) :
    I=Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
      {v | MinimalGenerator k q I v}) := by
  let J := Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
    {v | MinimalGenerator k q I v})
  have hmono (v : Fin q →₀ ℕ) (hv : MvPolynomial.monomial v (1:k)∈I) :
      MvPolynomial.monomial v (1:k)∈J := by
    obtain ⟨w,hw,hmin⟩ := minimal_divisor k q I v hv
    have hdvd : MvPolynomial.monomial w (1:k)∣MvPolynomial.monomial v (1:k) :=
      (MvPolynomial.monomial_dvd_monomial (r:=(1:k)) (s:=(1:k))).mpr ⟨Or.inr hw,dvd_rfl⟩
    obtain ⟨g,hg⟩ := hdvd
    rw [hg]
    exact J.mul_mem_right g (Ideal.subset_span ⟨w,hmin,rfl⟩)
  apply le_antisymm
  · intro f hf
    rw [f.as_sum]
    apply Ideal.sum_mem
    intro v hv
    have hs := J.restrictScalars k |>.smul_mem (f.coeff v) (hmono v (hI f hf v hv))
    change f.coeff v • MvPolynomial.monomial v (1:k)∈J at hs
    rw [MvPolynomial.smul_monomial,smul_eq_mul,mul_one] at hs
    exact hs
  · apply Ideal.span_le.mpr
    rintro _ ⟨v,hv,rfl⟩
    exact hv.1
end NSP14.Lex
