module
public import NSP14.Lex.MonomialExtension
public import NSP14.Lex.GenericDistraction
@[expose] public section
open scoped Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
open NSP14.Homological
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem quotientHilbert_eq_standard_card (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (n : ℕ) :
    quotientHilbert k q I hI n = Fintype.card
      {a : PolynomialDegreeIndex q n // a.val ∈ StandardExponent MonomialOrder.degLex I} := by
  let := standard_degree_finite k q I (n:ℤ)
  let := Fintype.ofFinite {a : StandardExponent MonomialOrder.degLex I // (a.val.degree:ℤ)=(n:ℤ)}
  change Module.finrank k ({a : StandardExponent MonomialOrder.degLex I //
    (a.val.degree:ℤ)=(n:ℤ)} →₀ k)=_
  rw [Module.finrank_finsupp_self]
  apply Fintype.card_congr
  exact {
    toFun := fun a => ⟨⟨a.val.val,by exact_mod_cast a.property⟩,a.val.property⟩
    invFun := fun a => ⟨⟨a.val.val,a.property⟩,by exact_mod_cast a.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem upper_finset_eq_of_card {α β : Type*} [Fintype α] [LinearOrder β]
    (f : α → β) (s t : Finset α)
    (hs : ∀ a ∈ s,∀ b,f a≤f b→b∈s)
    (ht : ∀ a ∈ t,∀ b,f a≤f b→b∈t) (hc : s.card=t.card) : s=t := by
  by_cases hst : s⊆t
  · exact Finset.eq_of_subset_of_card_le hst hc.ge
  · obtain ⟨a,ha,hat⟩ := Finset.not_subset.mp hst
    have hts : t⊆s := by
      intro b hb
      rcases le_total (f a) (f b) with hab|hba
      · exact hs a ha b hab
      · exact False.elim (hat (ht b hb a hba))
    exact (Finset.eq_of_subset_of_card_le hts hc.le).symm

theorem IsLex.eq_of_sameHilbert (I J : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hlI : IsLex k q I) (hlJ : IsLex k q J)
    (hH : ∀ n,quotientHilbert k q I hI n=quotientHilbert k q J hJ n) : I=J := by
  have hdeg (n : ℕ) :
      Finset.univ.filter (fun a : PolynomialDegreeIndex q n => MvPolynomial.monomial a.val (1:k)∈I)=
      Finset.univ.filter (fun a : PolynomialDegreeIndex q n => MvPolynomial.monomial a.val (1:k)∈J) := by
    apply upper_finset_eq_of_card (fun a : PolynomialDegreeIndex q n => MonomialOrder.lex.toSyn a.val)
    · intro a ha b hab
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
      exact hlI.2 _ _ (a.property.trans b.property.symm) hab ha
    · intro a ha b hab
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at ha ⊢
      exact hlJ.2 _ _ (a.property.trans b.property.symm) hab ha
    · have hc := hH n
      rw [quotientHilbert_eq_standard_card k q I hI n,
        quotientHilbert_eq_standard_card k q J hJ n] at hc
      simp_rw [standardExponent_iff_not_mem k q hlI.1] at hc
      simp_rw [standardExponent_iff_not_mem k q hlJ.1] at hc
      have he := Fintype.card_compl_eq_card_compl
        (fun a : PolynomialDegreeIndex q n => MvPolynomial.monomial a.val (1:k)∉I)
        (fun a : PolynomialDegreeIndex q n => MvPolynomial.monomial a.val (1:k)∉J) hc
      simpa only [not_not,Fintype.card_subtype] using he
  have hmem (a : Fin q →₀ ℕ) : MvPolynomial.monomial a (1:k)∈I ↔ MvPolynomial.monomial a (1:k)∈J := by
    have he := congrArg (fun s => (⟨a,rfl⟩ : PolynomialDegreeIndex q a.degree)∈s) (hdeg a.degree)
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using (Iff.of_eq he)
  rw [hlI.1.span k q,hlJ.1.span k q]
  congr 2
  ext a
  exact hmem a
end NSP14.Lex

namespace NSP14.Lex
variable (k L : Type) [Field k] [Field L] (q : ℕ)
/-- Lex supports with the same entire quotient Hilbert function agree across fields. -/
theorem IsLex.monomial_mem_iff_of_sameHilbert
    (I : Ideal (MvPolynomial (Fin q) k)) (J : Ideal (MvPolynomial (Fin q) L))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) L))
    (hlI : IsLex k q I) (hlJ : IsLex L q J)
    (hH : ∀ n,quotientHilbert k q I hI n=quotientHilbert L q J hJ n)
    (a : Fin q →₀ ℕ) :
    MvPolynomial.monomial a (1:k)∈I ↔ MvPolynomial.monomial a (1:L)∈J := by
  have he : monomialExtension k L q I=J :=
    IsLex.eq_of_sameHilbert L q _ J (monomialExtension_homogeneous k L q I) hJ
      (monomialExtension_isLex k L q I hlI) hlJ (fun n =>
        (monomialExtension_sameHilbert k L q I hI hlI.1 n).symm.trans (hH n))
  rw [← monomialExtension_mem_iff k L q I a,he]
end NSP14.Lex
