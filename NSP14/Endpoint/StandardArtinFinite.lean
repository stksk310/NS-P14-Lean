module
public import NSP14.Endpoint.StandardArtinLow
public import NSP14.Homological.FiniteDegreeSum
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k)) [Module.Finite k (MvPolynomial σ k ⧸ I)]

instance artinStandardsFinite : Finite (StandardExponent MonomialOrder.degLex I) :=
  Module.Finite.finite_basis (standardMonomialBasis MonomialOrder.degLex I)

noncomputable def artinLimit : ℕ := by
  letI := Fintype.ofFinite (StandardExponent MonomialOrder.degLex I)
  exact max 2 (Finset.univ.sup (fun p : StandardExponent MonomialOrder.degLex I => p.val.degree))

theorem artin_degree_bound (p : StandardExponent MonomialOrder.degLex I) : p.val.degree≤artinLimit k σ I := by
  let := Fintype.ofFinite (StandardExponent MonomialOrder.degLex I)
  exact (Finset.le_sup (f:=fun p : StandardExponent MonomialOrder.degLex I => p.val.degree)
    (Finset.mem_univ p)).trans (le_max_right _ _)

variable (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))

noncomputable def artinHilbert (n : ℕ) : ℕ := Module.finrank k ((artinGrading k σ I hI).piece n)

theorem artinHilbert_card (n : ℕ) : artinHilbert k σ I hI n=
    Nat.card {p : StandardExponent MonomialOrder.degLex I // p.val.degree=n} := by
  let := Fintype.ofFinite (StandardExponent MonomialOrder.degLex I)
  change Module.finrank k ({p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=(n:ℤ)} →₀ k)=_
  rw [Module.finrank_finsupp_self,Nat.card_eq_fintype_card]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (fun p => Nat.cast_inj)

theorem artinGrading_above (n : ℕ) (hn : artinLimit k σ I < n) :
    IsZero ((artinGrading k σ I hI).piece n) := by
  have : IsEmpty {p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=(n:ℤ)} :=
    ⟨fun p => by
      have hd : p.val.val.degree=n := by exact_mod_cast p.property
      have hb := artin_degree_bound k σ I p.val
      omega⟩
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (inferInstanceAs (Subsingleton ({p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=(n:ℤ)} →₀ k)))

theorem artinHilbert_sum : (∑ n∈Finset.range (artinLimit k σ I+1),artinHilbert k σ I hI n)=
    Module.finrank k (MvPolynomial σ k ⧸ I) := by
  let := Fintype.ofFinite (StandardExponent MonomialOrder.degLex I)
  have h := finite_degree_sum (fun p : StandardExponent MonomialOrder.degLex I => p.val.degree)
    (artinLimit k σ I) (artin_degree_bound k σ I) (fun _ => (1:ℚ))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,one_mul] at h
  simp_rw [←artinHilbert_card k σ I hI] at h
  rw [Module.finrank_eq_card_basis (standardMonomialBasis MonomialOrder.degLex I)]
  exact_mod_cast h.symm

variable (hproper : I≠⊤) (hlinear : ∀ f∈I, f.IsHomogeneous 1 → f=0)

include hproper hlinear in
theorem artinHilbert_zero : artinHilbert k σ I hI 0=1 := by
  let := Fintype.ofFinite (StandardExponent MonomialOrder.degLex I)
  change Module.finrank k ({p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=0} →₀ k)=_
  rw [Module.finrank_finsupp_self,←Nat.card_eq_fintype_card,
    Nat.card_congr (artinZeroEquiv k σ I hproper hI hlinear)]
  simp

include hproper hlinear in
theorem artinHilbert_one : artinHilbert k σ I hI 1=Fintype.card σ := by
  let := Fintype.ofFinite (StandardExponent MonomialOrder.degLex I)
  change Module.finrank k ({p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=1} →₀ k)=_
  rw [Module.finrank_finsupp_self,←Nat.card_eq_fintype_card,
    ←Nat.card_congr (artinOneEquiv k σ I hproper hI hlinear)]
  exact Nat.card_eq_fintype_card
end NSP14.Endpoint
