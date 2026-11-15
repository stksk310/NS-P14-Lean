module
public import NSP14.Lex.LexTailCorrection
@[expose] public section
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

/-- Actual degree-n monomials outside I, supported on the first j variables. -/
def standardPrefixCard (I : Ideal (MvPolynomial (Fin q) k)) (n j : ℕ) : ℕ :=
  Fintype.card {α : PolynomialDegreeIndex q n // MvPolynomial.monomial α.val (1:k)∉I ∧ maxVariable q α.val≤j}

theorem standardPrefixCard_sum (I : Ideal (MvPolynomial (Fin q) k)) (n : ℕ) :
    (∑ j∈Finset.range q,standardPrefixCard k q I n j)=standardDegreeGapSum k q I n := by
  let S := Finset.univ.filter (fun α : PolynomialDegreeIndex q n => MvPolynomial.monomial α.val (1:k)∉I)
  have hc (j : ℕ) : standardPrefixCard k q I n j=
      ∑ α∈S,if maxVariable q α.val≤j then 1 else 0 := by
    rw [← Finset.sum_filter]
    simp only [standardPrefixCard,Fintype.card_subtype,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,S,Finset.filter_filter]
  simp_rw [hc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  rw [← Finset.sum_filter]
  have he : (Finset.range q).filter (fun j => maxVariable q α.val≤j)=Finset.Ico (maxVariable q α.val) q := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    exact and_comm
  rw [he]
  simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul,Nat.cast_id,mul_one]

/-- The same K as the paper's double sum over S_(j-1)(n), with n≥2 and 1≤j≤q. -/
theorem lexCorrection_eq_prefix_sum (I : Ideal (MvPolynomial (Fin q) k)) (N : ℕ) :
    lexCorrection k q I N=∑ d∈Finset.range N,∑ j∈Finset.range q,standardPrefixCard k q I (d+2) j := by
  apply Finset.sum_congr rfl
  intro d _
  exact (standardPrefixCard_sum k q I (d+2)).symm


def maxGeneratorDegreeCard (I : Ideal (MvPolynomial (Fin q) k)) (n : ℕ) : ℕ :=
  Fintype.card {α : PolynomialDegreeIndex q n // MinimalGenerator k q I α.val ∧ maxVariable q α.val=q}

theorem top_binomial_indicator (α : Fin q →₀ ℕ) (hne : α≠0) (hq : 1≤q) :
    (maxVariable q α-1).choose (q-1)=if maxVariable q α=q then 1 else 0 := by
  have hb := maxVariable_le_variables q α
  obtain ⟨r,_,hr,_⟩ := maxVariable_spec q α hne
  by_cases he : maxVariable q α=q
  · simp only [he,Nat.choose_self,ite_true]
  · rw [ite_eq_right he]
    apply Nat.choose_eq_zero_of_lt
    omega

theorem IsStronglyStable.top_gradedBetti_eq_generator_card
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hp : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (hq : 1≤q) (n : ℕ) :
    quotientGradedBetti k q I hHom q ((n:ℤ)+((q-1:ℕ):ℤ))=maxGeneratorDegreeCard k q I n := by
  have hh := hI.graded_ek_degree k q I hp hHom n (q-1)
  rw [Nat.sub_add_cancel hq] at hh
  rw [hh]
  let S := Finset.univ.filter (fun α : PolynomialDegreeIndex q n => MinimalGenerator k q I α.val)
  calc
    (∑ α : MinimalDegreeMonomial k q I n,(maxVariable q α.val.val-1).choose (q-1))=
        ∑ α∈S,(maxVariable q α.val-1).choose (q-1) := (Finset.sum_subtype (p:=fun α : PolynomialDegreeIndex q n => MinimalGenerator k q I α.val) S
          (by intro α; simp [S])
          (fun α : PolynomialDegreeIndex q n => (maxVariable q α.val-1).choose (q-1))).symm
    _=∑ α∈S,if maxVariable q α.val=q then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro α hα
      have hm : MinimalGenerator k q I α.val := (Finset.mem_filter.mp hα).2
      exact top_binomial_indicator q α.val (minimalGenerator_ne_zero q k I hp α.val hm) hq
    _=maxGeneratorDegreeCard k q I n := by
      rw [← Finset.sum_filter]
      simp only [S,Finset.filter_filter,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,
        maxGeneratorDegreeCard,Fintype.card_subtype]

theorem standardPrefixCard_eq_sum (I : Ideal (MvPolynomial (Fin q) k)) (n j : ℕ) :
    standardPrefixCard k q I n j=
      ∑ α∈Finset.univ.filter (fun α : PolynomialDegreeIndex q n => MvPolynomial.monomial α.val (1:k)∉I),
        if maxVariable q α.val≤j then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp only [standardPrefixCard,Fintype.card_subtype,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one,Finset.filter_filter]

theorem standard_top_partition (I : Ideal (MvPolynomial (Fin q) k))
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (hm : IsMonomial k q I)
    (hq : 1≤q) (n : ℕ) (hn : 1≤n) :
    standardDegreeBinomialSum k q I n (q-1)+standardPrefixCard k q I n (q-1)=quotientHilbert k q I hHom n := by
  have hc : quotientHilbert k q I hHom n=
      (Finset.univ.filter (fun α : PolynomialDegreeIndex q n => MvPolynomial.monomial α.val (1:k)∉I)).card := by
    rw [quotientHilbert_eq_standard_card]
    simp_rw [standardExponent_iff_not_mem k q hm]
    exact Fintype.card_subtype _
  rw [standardPrefixCard_eq_sum,standardDegreeBinomialSum,← Finset.sum_add_distrib,hc]
  calc
    (∑ α∈Finset.univ.filter (fun α : PolynomialDegreeIndex q n => MvPolynomial.monomial α.val (1:k)∉I),
      ((maxVariable q α.val-1).choose (q-1)+(if maxVariable q α.val≤q-1 then 1 else 0)))=
        ∑ _α∈Finset.univ.filter (fun α : PolynomialDegreeIndex q n => MvPolynomial.monomial α.val (1:k)∉I),1 := by
      apply Finset.sum_congr rfl
      intro α _
      have hne : α.val≠0 := by intro he; have hd:=α.property; rw [he,map_zero] at hd; omega
      rw [top_binomial_indicator q α.val hne hq]
      have hb := maxVariable_le_variables q α.val
      split_ifs <;> omega
    _=_ := by simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one]

/-- Additive form of the actual g_j(n) recurrence, for any prefix ideal with j=q variables. -/
theorem IsStronglyStable.max_generator_recurrence
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hp : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (hq : 1≤q) (d : ℕ) :
    maxGeneratorDegreeCard k q I (d+1)+quotientHilbert k q I hHom (d+1)=
      quotientHilbert k q I hHom d+standardPrefixCard k q I (d+1) (q-1) := by
  have hh := hI.standard_graded_binomial_identity k q I hp hHom d (q-1)
  rw [Nat.sub_add_cancel hq,Nat.choose_self,mul_one,
    hI.top_gradedBetti_eq_generator_card k q I hp hHom hq] at hh
  have hz : standardDegreeBinomialSum k q I d q=0 := by
    apply Finset.sum_eq_zero
    intro α _
    exact Nat.choose_eq_zero_of_lt (by have hb:=maxVariable_le_variables q α.val; omega)
  rw [hz,add_zero] at hh
  have hc := standard_top_partition k q I hHom hI.1 hq (d+1) (by omega)
  omega
end NSP14.Lex
