module
public import NSP14.Lex.SuffixVariableRestriction
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (s r : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra
theorem IsLex.standard_tail_support (I : Ideal (MvPolynomial (Fin (s+r)) k))
    (hI : IsLex k (s+r) I)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (s+r)) k))
    (hH2 : quotientHilbert k (s+r) I hHom 2≤Fintype.card (PolynomialDegreeIndex r 2))
    (α : Fin (s+r) →₀ ℕ) (hdeg : 2≤α.degree) (hα : MvPolynomial.monomial α (1:k)∉I) :
    ∀ i,i.val<s → α i=0 := by
  intro i his
  by_contra hzero
  have hi : 0<α i := Nat.pos_of_ne_zero hzero
  have hs : Finsupp.single i 1≤α := by
    intro l
    by_cases he : i=l
    · subst l; simpa using (Nat.succ_le_of_lt hi)
    · simp only [Finsupp.single_eq_of_ne' he]; exact Nat.zero_le _
  let β := α-Finsupp.single i 1
  have hadd : β+Finsupp.single i 1=α := tsub_add_cancel_of_le hs
  have hd : β.degree+1=α.degree := by have hh:=congrArg Finsupp.degree hadd; simpa only [map_add,Finsupp.degree_single] using hh
  have hβ : β≠0 := by intro he; rw [he,map_zero] at hd; omega
  obtain ⟨j,hj,_,_⟩ := maxVariable_spec (s+r) β hβ
  have hjs : Finsupp.single j 1≤β := by
    intro l
    by_cases he : j=l
    · subst l; simpa using (Nat.succ_le_of_lt hj)
    · simp only [Finsupp.single_eq_of_ne' he]; exact Nat.zero_le _
  let w := Finsupp.single i 1+Finsupp.single j 1
  have hwd : w.degree=2 := by simp only [w,map_add,Finsupp.degree_single]
  have hwa : w≤α := by
    rw [← hadd]
    intro l
    have hh := hjs l
    simp only [w,Finsupp.add_apply] at hh ⊢
    omega
  have hwi : 0<w i := by simp only [w,Finsupp.add_apply,Finsupp.single_eq_same]; omega
  have hwnot : MvPolynomial.monomial w (1:k)∉I := fun hw => hα (monomial_mem_of_le k (s+r) I w α hw hwa)
  have hws : w.support.Nonempty := ⟨i,Finsupp.mem_support_iff.mpr (by omega)⟩
  let ℓ := w.support.min' hws
  have hℓw : 0<w ℓ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (Finset.min'_mem w.support hws))
  have hℓi : ℓ≤ i := Finset.min'_le w.support i (Finsupp.mem_support_iff.mpr (by omega))
  have hℓs : ℓ.val<s := by change ℓ.val≤ i.val at hℓi; omega
  have hbefore (l : Fin (s+r)) (hl : l<ℓ) : w l=0 := by
    by_contra hn
    have hh := Finset.min'_le w.support l (Finsupp.mem_support_iff.mpr hn)
    exact not_lt_of_ge hh hl
  have htail (γ : PolynomialDegreeIndex r 2) : MvPolynomial.monomial (suffixExponent s r γ.val) (1:k)∉I := by
    intro hγ
    apply hwnot
    have hlex : MonomialOrder.lex.toSyn (suffixExponent s r γ.val)<MonomialOrder.lex.toSyn w := by
      change Finsupp.Lex (· < ·) (· < ·) (suffixExponent s r γ.val) w
      refine ⟨ℓ,?_,?_⟩
      · intro l hl
        rw [hbefore l hl,suffixExponent_before s r γ.val l (by change l.val<ℓ.val at hl; omega)]
      · rw [suffixExponent_before s r γ.val ℓ hℓs]
        exact hℓw
    exact hI.2 _ _ ((suffixExponent_degree s r γ.val).trans (γ.property.trans hwd.symm)) hlex.le hγ
  let f : Option (PolynomialDegreeIndex r 2) →
      {γ : PolynomialDegreeIndex (s+r) 2 // MvPolynomial.monomial γ.val (1:k)∉I} := fun x =>
    match x with
    | none => ⟨⟨w,hwd⟩,hwnot⟩
    | some γ => ⟨⟨suffixExponent s r γ.val,(suffixExponent_degree s r γ.val).trans γ.property⟩,htail γ⟩
  have hf : Function.Injective f := by
    intro a b he
    have hv := congrArg (fun z : {γ : PolynomialDegreeIndex (s+r) 2 // MvPolynomial.monomial γ.val (1:k)∉I} => z.val.val) he
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some b =>
        have hh := congrArg (fun z => z i) hv
        change w i=suffixExponent s r b.val i at hh
        rw [suffixExponent_before s r b.val i his] at hh
        omega
    | some a =>
      cases b with
      | none =>
        have hh := congrArg (fun z => z i) hv
        change suffixExponent s r a.val i=w i at hh
        rw [suffixExponent_before s r a.val i his] at hh
        omega
      | some b =>
        congr 1
        apply Subtype.ext
        exact suffixExponent_injective s r hv
  have hc := Fintype.card_le_of_injective f hf
  have hHF : quotientHilbert k (s+r) I hHom 2=
      Fintype.card {γ : PolynomialDegreeIndex (s+r) 2 // MvPolynomial.monomial γ.val (1:k)∉I} := by
    rw [quotientHilbert_eq_standard_card]
    simp_rw [standardExponent_iff_not_mem k (s+r) hI.1]
  rw [Fintype.card_option] at hc
  omega


theorem IsMonomial.homogeneous (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsMonomial k q I) :
    I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k) := by
  rw [hI.span k q]
  apply Ideal.homogeneous_span
  rintro _ ⟨v,_,rfl⟩
  exact ⟨v.degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩

def suffixStandardDegreeEquiv (I : Ideal (MvPolynomial (Fin (s+r)) k)) (n : ℕ)
    (htail : ∀ α : PolynomialDegreeIndex (s+r) n,MvPolynomial.monomial α.val (1:k)∉I → ∀ j,j.val<s → α.val j=0) :
    {α : PolynomialDegreeIndex r n // MvPolynomial.monomial α.val (1:k)∉suffixVariableIdeal k s r I} ≃
      {α : PolynomialDegreeIndex (s+r) n // MvPolynomial.monomial α.val (1:k)∉I} where
  toFun α := ⟨⟨suffixExponent s r α.val.val,(suffixExponent_degree s r α.val.val).trans α.val.property⟩,
    fun hm => α.property ((suffixVariableIdeal_monomial k s r I α.val.val).mpr hm)⟩
  invFun α := ⟨⟨suffixHead s r α.val.val,(suffixHead_degree s r α.val.val (htail α.val α.property)).trans α.val.property⟩,
    fun hm => α.property (by
      have hh := (suffixVariableIdeal_monomial k s r I _).mp hm
      rw [suffixExponent_head s r α.val.val (htail α.val α.property)] at hh
      exact hh)⟩
  left_inv α := Subtype.ext (Subtype.ext (suffixHead_suffix s r α.val.val))
  right_inv α := Subtype.ext (Subtype.ext (suffixExponent_head s r α.val.val (htail α.val α.property)))

theorem IsLex.suffix_sameHilbert_high (I : Ideal (MvPolynomial (Fin (s+r)) k))
    (hI : IsLex k (s+r) I)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin (s+r)) k))
    (hH2 : quotientHilbert k (s+r) I hHom 2≤Fintype.card (PolynomialDegreeIndex r 2))
    (hHomS : (suffixVariableIdeal k s r I).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin r) k))
    (n : ℕ) (hn : 2≤n) :
    quotientHilbert k r (suffixVariableIdeal k s r I) hHomS n=quotientHilbert k (s+r) I hHom n := by
  rw [quotientHilbert_eq_standard_card,quotientHilbert_eq_standard_card]
  simp_rw [standardExponent_iff_not_mem k r (suffixVariableIdeal_isMonomial k s r I hI.1)]
  simp_rw [standardExponent_iff_not_mem k (s+r) hI.1]
  exact Fintype.card_congr (suffixStandardDegreeEquiv k s r I n
    (fun α hα => hI.standard_tail_support k s r I hHom hH2 α.val (by rw [α.property]; exact hn) hα))
end NSP14.Lex

