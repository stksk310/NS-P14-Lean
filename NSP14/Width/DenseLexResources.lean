module
public import NSP14.Width.CoreLexPresentation
public import NSP14.Lex.TailHarmonic
public import NSP14.Width.DenseResources
public import NSP14.Endpoint.CoreHilbertSum
@[expose] public section
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem coreHilbert_high_sum (hu : 2≤D.u) :
    (∑ d∈Finset.range (D.u-2),D.coreHilbert k (d+2))+D.q+1=D.coreP k := by
  have hh := D.coreHilbert_sum k
  have he : D.u=D.u-2+1+1 := by omega
  rw [he,Finset.sum_range_succ',Finset.sum_range_succ'] at hh
  simp only [D.coreHilbert_zero k,D.coreHilbert_one k,Nat.zero_add] at hh
  exact hh

theorem dense_lex_correction_bound (t r : ℕ) (hu : D.u=D.q+1+t) (ht : t≤D.q)
    (hr : r≤D.q) (hr2 : 2≤r) (hchoose : 2*t≤(r+1).choose 2)
    (L : Ideal (MvPolynomial (Fin D.q) k))
    (hL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin D.q) k)) (hlL : Lex.IsLex k D.q L)
    (hHF : ∀ n,Lex.quotientHilbert k D.q L hL n=D.coreHilbert k n) :
    (Lex.lexCorrection k D.q L (D.u-2):ℚ)≤2*(t:ℚ)*((r-1:ℕ):ℚ)/3 := by
  have hq2 : 2≤D.q := D.q_two
  have hu3 : 3≤D.u := by omega
  have hp : L≠⊤ := by
    intro he
    have hh := hHF 0
    rw [D.coreHilbert_zero k] at hh
    have hz : Lex.quotientHilbert k D.q L hL 0=0 := by
      simpa only [he] using Lex.quotientHilbert_top_zero k D.q (he ▸ hL) 0
    omega
  have hsum := D.coreHilbert_high_sum k (by omega)
  have hP := D.dense_coreP k t hu ht
  have htail : (∑ d∈Finset.range (D.u-2),D.coreHilbert k (d+2))≤2*t := by omega
  have h2tail : D.coreHilbert k 2≤∑ d∈Finset.range (D.u-2),D.coreHilbert k (d+2) := by
    have hh := Finset.single_le_sum (s:=Finset.range (D.u-2)) (f:=fun d => D.coreHilbert k (d+2))
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega : 0<D.u-2))
    simpa only [Nat.zero_add] using hh
  have hH2 : Lex.quotientHilbert k D.q L hL 2≤Fintype.card (Lex.PolynomialDegreeIndex r 2) := by
    rw [hHF 2,Lex.degreeTwo_card]
    omega
  have hN (n : ℕ) (hn : D.u-2+1<n) : Lex.quotientHilbert k D.q L hL n=0 := by
    rw [hHF n]
    exact D.coreHilbert_above k n (by omega)
  have hk := hlL.correction_tail_third_bound k D.q L hp hL (D.u-2) r hr hr2 hH2 hN
    ((hHF 0).trans (D.coreHilbert_zero k)) ((hHF 1).trans (D.coreHilbert_one k))
  simp_rw [hHF] at hk
  have htailQ : (∑ d∈Finset.range (D.u-2),(D.coreHilbert k (d+2):ℚ))≤2*(t:ℚ) := by exact_mod_cast htail
  have hm := mul_le_mul_of_nonneg_left htailQ (Nat.cast_nonneg (r-1) : (0:ℚ)≤((r-1:ℕ):ℚ))
  have hb := hk.trans (div_le_div_of_nonneg_right hm (by norm_num : (0:ℚ)≤3))
  convert hb using 1; ring


theorem dense_core_lex_bound (t : ℕ) (hu : D.u=D.q+1+t) (ht : t≤D.q) (hq : 4≤D.q) :
    ∃ K : ℕ,(∀ i : ℕ,1 ≤ i → totalBetti k D.a (D.QCoreModule k) i≤
      i*(D.q+1).choose (i+1)+K*(D.q-1).choose (i-1)) ∧
      (t=2 → K≤2) ∧ (t=3 → K≤4) ∧ (4≤t → 3*K≤2*t*(t-1)) := by
  obtain ⟨L,hL,hlL,hHF,hbetti⟩ := D.exists_core_lex k
  let K := Lex.lexCorrection k D.q L (D.u-2)
  have hu3 : 3≤D.u := by omega
  have h0 : Lex.quotientHilbert k D.q L hL 0=1 := (hHF 0).trans (D.coreHilbert_zero k)
  have h1 : Lex.quotientHilbert k D.q L hL 1=D.q := (hHF 1).trans (D.coreHilbert_one k)
  have hp : L≠⊤ := by
    intro he
    have hz : Lex.quotientHilbert k D.q L hL 0=0 := by
      simpa only [he] using Lex.quotientHilbert_top_zero k D.q (he ▸ hL) 0
    omega
  have hN (n : ℕ) (hn : D.u-2+1<n) : Lex.quotientHilbert k D.q L hL n=0 := by
    rw [hHF n]
    exact D.coreHilbert_above k n (by omega)
  refine ⟨K,?_,?_,?_,?_⟩
  · intro i hi
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
    have hh := (hbetti (j+1) (by omega)).trans (hlL.total_betti_le_correction k D.q L hp hL (D.u-2) j hN h0 h1)
    simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.add_assoc] using hh
  · intro ht2
    have hh := D.dense_lex_correction_bound k t 3 hu ht (by omega) (by omega) (by rw [ht2]; decide) L hL hlL hHF
    change (K:ℚ)≤_ at hh
    have hbound : (3:ℚ)*(K:ℚ)≤8 := by rw [ht2] at hh; norm_num at hh; linarith only [hh]
    have hNat : 3*K≤8 := by exact_mod_cast hbound
    omega
  · intro ht3
    have hh := D.dense_lex_correction_bound k t 3 hu ht (by omega) (by omega) (by rw [ht3]; decide) L hL hlL hHF
    change (K:ℚ)≤_ at hh
    rw [ht3] at hh
    norm_num at hh
    exact_mod_cast hh
  · intro ht4
    have hchoose : 2*t≤(t+1).choose 2 := by
      have hc := Nat.add_one_mul_choose_eq t 1
      rw [Nat.choose_one_right] at hc
      have hm := Nat.mul_le_mul_left t (show 4≤t+1 by omega)
      nlinarith only [hc,hm]
    have hh := D.dense_lex_correction_bound k t t hu ht ht (by omega) hchoose L hL hlL hHF
    change (K:ℚ)≤_ at hh
    have hbound : (3:ℚ)*(K:ℚ)≤2*(t:ℚ)*((t-1:ℕ):ℚ) := by linarith only [hh]
    exact_mod_cast hbound
end NSP14.Endpoint.Data

