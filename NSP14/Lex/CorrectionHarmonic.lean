module
public import NSP14.Lex.StandardBettiWeights
public import NSP14.Endpoint.StandardArtinGeneration
@[expose] public section
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem finite_quotient_of_Hilbert_cutoff (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (N : ℕ) (hN : ∀ n,N<n → quotientHilbert k q I hI n=0) :
    Module.Finite k (MvPolynomial (Fin q) k ⧸ I) := by
  have hd (p : StandardExponent MonomialOrder.degLex I) : p.val.degree≤N := by
    by_contra hn
    have hp : 0<quotientHilbert k q I hI p.val.degree := by
      rw [quotientHilbert_eq_standard_card]
      apply Fintype.card_pos_iff.mpr
      exact ⟨⟨⟨p.val,rfl⟩,p.property⟩⟩
    have hz := hN p.val.degree (by omega)
    omega
  let f : StandardExponent MonomialOrder.degLex I → (n : Fin (N+1)) × PolynomialDegreeIndex q n.val :=
    fun p => ⟨⟨p.val.degree,by have hh:=hd p; omega⟩,⟨p.val,rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun z : (n : Fin (N+1)) × PolynomialDegreeIndex q n.val => z.2.val) he
  let : Finite (StandardExponent MonomialOrder.degLex I) := Finite.of_injective f hf
  exact Module.Finite.of_basis (standardMonomialBasis MonomialOrder.degLex I)

theorem monomial_no_linear_of_Hilbert_one (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (hmono : IsMonomial k q I)
    (hH1 : quotientHilbert k q I hI 1=q) : ∀ f∈I,f.IsHomogeneous 1 → f=0 := by
  have hc := idealDegreeCard_add_hilbert k q I hI hmono 1
  rw [hH1,degreeOne_card] at hc
  have hcz : idealDegreeCard k q I 1=0 := by omega
  intro f hf hhom
  ext v
  by_contra hn
  have hcoeff : f.coeff v≠0 := by simpa only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using hn
  have hv := MvPolynomial.mem_support_iff.mpr hcoeff
  have hmem := hmono f hf v hv
  have hd : v.degree=1 := by
    rw [MvPolynomial.IsHomogeneous,MvPolynomial.IsWeightedHomogeneous] at hhom
    exact (DFunLike.congr_fun Finsupp.degree_eq_weight_one v).trans (hhom hcoeff)
  have hp : 0< idealDegreeCard k q I 1 := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨⟨v,hd⟩,hmem⟩⟩
  omega

theorem IsLex.correction_harmonic_bound (I : Ideal (MvPolynomial (Fin q) k))
    (hI : IsLex k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N : ℕ)
    (hq : 2≤q) (hN : ∀ n,N+1<n → quotientHilbert k q I hHom n=0)
    (hH0 : quotientHilbert k q I hHom 0=1) (hH1 : quotientHilbert k q I hHom 1=q) :
    (lexCorrection k q I N:ℚ)≤
      ∑ d∈Finset.range N,((q-1:ℕ):ℚ)*(quotientHilbert k q I hHom (d+2):ℚ)/((d:ℚ)+3) := by
  let : Module.Finite k (MvPolynomial (Fin q) k ⧸ I) := finite_quotient_of_Hilbert_cutoff k q I hHom (N+1) hN
  let : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp (by omega)
  have hlin := monomial_no_linear_of_Hilbert_one k q I hHom hI.1 hH1
  have hbound := NSP14.Endpoint.cyclic_first_harmonic k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I)
    (NSP14.Endpoint.artinGrading k (Fin q) I hHom) (N+1)
    (NSP14.Endpoint.artin_generated_zero k (Fin q) I hproper hHom hlin) (by
      intro n hn
      apply ModuleCat.isZero_iff_subsingleton.mpr
      apply (Module.finrank_zero_iff (R:=k)).mp
      change quotientHilbert k q I hHom (0+n)=0
      simpa only [Nat.zero_add] using hN n (by omega))
    hH0 (NSP14.Endpoint.artin_totalBetti_zero_general k (Fin q) I hproper hHom)
  simp only [Fintype.card_fin] at hbound
  change (_:ℚ)≤(q:ℚ)+∑ n∈Finset.range (N+1),((q-1:ℕ):ℚ)*(quotientHilbert k q I hHom (n+1):ℚ)/((n:ℚ)+2) at hbound
  rw [Finset.sum_range_succ',hH1] at hbound
  have hshift : (∑ d∈Finset.range N,((q-1:ℕ):ℚ)*(quotientHilbert k q I hHom (d+1+1):ℚ)/(((d+1:ℕ):ℚ)+2))=
      ∑ d∈Finset.range N,((q-1:ℕ):ℚ)*(quotientHilbert k q I hHom (d+2):ℚ)/((d:ℚ)+3) := by
    apply Finset.sum_congr rfl
    intro d _
    rw [show d+1+1=d+2 by omega]
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  rw [hshift] at hbound
  have hrow := hI.first_betti_eq_correction k q I hproper hHom N hN hH0 hH1
  have hrowQ : (totalBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I) 1:ℚ)=
      ((q+1).choose 2:ℚ)+(lexCorrection k q I N:ℚ) := by exact_mod_cast hrow
  have htwo : (q:ℚ)*((q:ℚ)+1)=((q+1).choose 2:ℚ)*2 := by
    have hh := Nat.add_one_mul_choose_eq q 1
    rw [Nat.choose_one_right] at hh
    have hh' : q*(q+1)=(q+1).choose 2*2 := by nlinarith only [hh]
    exact_mod_cast hh'
  have hcast : ((q-1:ℕ):ℚ)=(q:ℚ)-1 := Nat.cast_sub (by omega)
  rw [hcast] at hbound
  norm_num only [Nat.cast_zero,zero_add] at hbound
  rw [hcast]
  nlinarith only [hbound,hrowQ,htwo]

theorem IsLex.correction_third_bound (I : Ideal (MvPolynomial (Fin q) k))
    (hI : IsLex k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (N : ℕ)
    (hq : 2≤q) (hN : ∀ n,N+1<n → quotientHilbert k q I hHom n=0)
    (hH0 : quotientHilbert k q I hHom 0=1) (hH1 : quotientHilbert k q I hHom 1=q) :
    (lexCorrection k q I N:ℚ)≤((q-1:ℕ):ℚ)*(∑ d∈Finset.range N,(quotientHilbert k q I hHom (d+2):ℚ))/3 := by
  apply (hI.correction_harmonic_bound k q I hproper hHom N hq hN hH0 hH1).trans
  calc
    (∑ d∈Finset.range N,((q-1:ℕ):ℚ)*(quotientHilbert k q I hHom (d+2):ℚ)/((d:ℚ)+3))≤
        ∑ d∈Finset.range N,((q-1:ℕ):ℚ)*(quotientHilbert k q I hHom (d+2):ℚ)/3 := by
      apply Finset.sum_le_sum
      intro d _
      exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by norm_num) (by have hh: (0:ℚ)≤(d:ℚ):=Nat.cast_nonneg d; linarith)
    _=((q-1:ℕ):ℚ)*(∑ d∈Finset.range N,(quotientHilbert k q I hHom (d+2):ℚ))/3 := by
      rw [← Finset.sum_div,← Finset.mul_sum]


end NSP14.Lex
