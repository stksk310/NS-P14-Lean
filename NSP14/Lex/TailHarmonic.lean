module
public import NSP14.Lex.CorrectionHarmonic
public import NSP14.Lex.LexTailCorrection
@[expose] public section
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
theorem IsLex.correction_tail_harmonic_bound (I : Ideal (MvPolynomial (Fin q) k))
    (hI : IsLex k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N r : ℕ)
    (hr : r≤q) (hr2 : 2≤r)
    (hH2 : quotientHilbert k q I hHom 2≤Fintype.card (PolynomialDegreeIndex r 2))
    (hN : ∀ n,N+1<n → quotientHilbert k q I hHom n=0)
    (hH0 : quotientHilbert k q I hHom 0=1) (hH1 : quotientHilbert k q I hHom 1=q) :
    (lexCorrection k q I N:ℚ)≤∑ d∈Finset.range N,((r-1:ℕ):ℚ)*(quotientHilbert k q I hHom (d+2):ℚ)/((d:ℚ)+3) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_add_of_le' hr
  let B := suffixVariableIdeal k s r I
  have hlB : IsLex k r B := suffixVariableIdeal_isLex k s r I hI
  have hHomB : B.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin r) k) := hlB.1.homogeneous k r B
  have hpB : B≠⊤ := by
    intro he
    have hb1 : (1:MvPolynomial (Fin r) k)∈B := by rw [he]; trivial
    have hi1 : (1:MvPolynomial (Fin (s+r)) k)∈I := by
      change MvPolynomial.rename (Fin.natAdd s) 1∈I at hb1
      simpa only [map_one] using hb1
    exact hproper ((Ideal.eq_top_iff_one I).mpr hi1)
  have hHF (n : ℕ) (hn : 2≤n) : quotientHilbert k r B hHomB n=quotientHilbert k (s+r) I hHom n :=
    hI.suffix_sameHilbert_high k s r I hHom hH2 hHomB n hn
  have hNB (n : ℕ) (hn : N+1<n) : quotientHilbert k r B hHomB n=0 := (hHF n (by omega)).trans (hN n hn)
  let : Module.Finite k (MvPolynomial (Fin r) k ⧸ B) := finite_quotient_of_Hilbert_cutoff k r B hHomB (N+1) hNB
  have hlinI := monomial_no_linear_of_Hilbert_one k (s+r) I hHom hI.1 hH1
  have hlinB : ∀ f∈B,f.IsHomogeneous 1 → f=0 := by
    intro f hf hhom
    have hh : MvPolynomial.rename (Fin.natAdd s) f=0 := hlinI _ hf
      ((MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff (Fin.natAdd_injective r s)).mpr hhom)
    apply MvPolynomial.rename_injective (Fin.natAdd s) (Fin.natAdd_injective r s)
    simpa only [map_zero] using hh
  have h0B : quotientHilbert k r B hHomB 0=1 :=
    NSP14.Endpoint.artinGrading_zero_dim_general k (Fin r) B hpB hHomB
  have h1B : quotientHilbert k r B hHomB 1=r := by
    simpa only [NSP14.Endpoint.artinHilbert,quotientHilbert,Fintype.card_fin] using
      NSP14.Endpoint.artinHilbert_one k (Fin r) B hHomB hpB hlinB
  have hk := hlB.correction_harmonic_bound k r B hpB hHomB N hr2 hNB h0B h1B
  have hK : lexCorrection k r B N=lexCorrection k (s+r) I N := hI.suffix_sameCorrection k s r I hHom hH2 N
  have hsum : (∑ d∈Finset.range N,((r-1:ℕ):ℚ)*(quotientHilbert k r B hHomB (d+2):ℚ)/((d:ℚ)+3))=
      ∑ d∈Finset.range N,((r-1:ℕ):ℚ)*(quotientHilbert k (s+r) I hHom (d+2):ℚ)/((d:ℚ)+3) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [hHF (d+2) (by omega)]
  rw [hK,hsum] at hk
  exact hk

theorem IsLex.correction_tail_third_bound (I : Ideal (MvPolynomial (Fin q) k))
    (hI : IsLex k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N r : ℕ)
    (hr : r≤q) (hr2 : 2≤r)
    (hH2 : quotientHilbert k q I hHom 2≤Fintype.card (PolynomialDegreeIndex r 2))
    (hN : ∀ n,N+1<n → quotientHilbert k q I hHom n=0)
    (hH0 : quotientHilbert k q I hHom 0=1) (hH1 : quotientHilbert k q I hHom 1=q) :
    (lexCorrection k q I N:ℚ)≤((r-1:ℕ):ℚ)*(∑ d∈Finset.range N,(quotientHilbert k q I hHom (d+2):ℚ))/3 := by
  apply (hI.correction_tail_harmonic_bound k q I hproper hHom N r hr hr2 hH2 hN hH0 hH1).trans
  calc
    (∑ d∈Finset.range N,((r-1:ℕ):ℚ)*(quotientHilbert k q I hHom (d+2):ℚ)/((d:ℚ)+3))≤
        ∑ d∈Finset.range N,((r-1:ℕ):ℚ)*(quotientHilbert k q I hHom (d+2):ℚ)/3 := by
      apply Finset.sum_le_sum
      intro d _
      exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num)
        (by have hh : (0:ℚ)≤(d:ℚ) := Nat.cast_nonneg d; linarith)
    _=((r-1:ℕ):ℚ)*(∑ d∈Finset.range N,(quotientHilbert k q I hHom (d+2):ℚ))/3 := by
      rw [← Finset.sum_div,← Finset.mul_sum]
end NSP14.Lex

namespace NSP14.Lex
theorem degreeTwo_card (q : ℕ) : Fintype.card (PolynomialDegreeIndex q 2)=(q+1).choose 2 := by
  rw [Fintype.card_congr (degreeIndexSymEquiv q 2),Sym.card_sym_eq_choose,Fintype.card_fin]
  rw [show q+2-1=q+1 by omega]
end NSP14.Lex

