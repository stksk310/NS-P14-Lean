module
public import NSP14.Lex.PrefixVariableRestriction
public import Mathlib.Data.Nat.Choose.Sum
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex

theorem sum_choose_column (n i : ℕ) : (∑ r∈Finset.range n,r.choose i)=n.choose (i+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,Nat.choose_succ_succ]
    exact Nat.add_comm _ _

theorem choose_as_max_sum (q m i : ℕ) (hm : m≤q) :
    (m-1).choose (i+1)=∑ r∈Finset.range q,if r+1<m then r.choose i else 0 := by
  rw [← sum_choose_column,← Finset.sum_filter]
  have hf : (Finset.range q).filter (fun r => r+1<m)=Finset.range (m-1) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [hf]

theorem sum_choose_by_tails {A : Type*} (s : Finset A) (f : A → ℕ) (q i : ℕ)
    (hbound : ∀ a∈s,f a≤q) :
    (∑ a∈s,(f a-1).choose (i+1))=
      ∑ r∈Finset.range q,(s.filter (fun a => r+1<f a)).card*r.choose i := by
  calc
    (∑ a∈s,(f a-1).choose (i+1))=
        ∑ a∈s,∑ r∈Finset.range q,if r+1<f a then r.choose i else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact choose_as_max_sum q (f a) i (hbound a ha)
    _=∑ r∈Finset.range q,∑ a∈s,if r+1<f a then r.choose i else 0 := Finset.sum_comm
    _=∑ r∈Finset.range q,(s.filter (fun a => r+1<f a)).card*r.choose i := by
      apply Finset.sum_congr rfl
      intro r _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id]

/-- Larger lower-prefix counts with the same total size give smaller increasing
binomial weights. All quantities are natural-number cardinalities. -/
theorem sum_choose_le_of_cumulative {A : Type*} (s t : Finset A) (f : A → ℕ) (q i : ℕ)
    (hs : ∀ a∈s,f a≤q) (ht : ∀ a∈t,f a≤q) (hcard : s.card=t.card)
    (hcum : ∀ r,(t.filter (fun a => f a≤r)).card≤(s.filter (fun a => f a≤r)).card) :
    (∑ a∈s,(f a-1).choose i)≤∑ a∈t,(f a-1).choose i := by
  cases i with
  | zero =>
    simpa only [Nat.choose_zero_right,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one] using hcard.le
  | succ i =>
    rw [sum_choose_by_tails s f q i hs,sum_choose_by_tails t f q i ht]
    apply Finset.sum_le_sum
    intro r _
    apply Nat.mul_le_mul_right
    have hsc := Finset.card_filter_add_card_filter_not (s:=s) (p:=fun a => f a≤r+1)
    have htc := Finset.card_filter_add_card_filter_not (s:=t) (p:=fun a => f a≤r+1)
    simp only [not_le] at hsc htc
    have hh := hcum (r+1)
    omega
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

def degreeBinomialSum (I : Ideal (MvPolynomial (Fin q) k)) (d i : ℕ) : ℕ :=
  ∑ α∈Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∈I),
    (maxVariable q α.val-1).choose i

theorem IsStronglyStable.binomial_degree_sum_le_lex
    (I L : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hL : IsLex k q L)
    (d i : ℕ) (hcard : idealDegreeCard k q I d=idealDegreeCard k q L d) :
    degreeBinomialSum k q I d i≤degreeBinomialSum k q L d i := by
  let S := Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∈I)
  let T := Finset.univ.filter (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∈L)
  have hc : S.card=T.card := by simpa only [idealDegreeCard,Fintype.card_subtype] using hcard
  have hcum (r : ℕ) : (T.filter (fun α => maxVariable q α.val≤r)).card≤
      (S.filter (fun α => maxVariable q α.val≤r)).card := by
    have hh := hI.cumulative_le_lex k q I L hL d hcard.ge r
    simpa only [cumulativeDegreeCard,Fintype.card_subtype,T,S,Finset.filter_filter] using hh
  exact sum_choose_le_of_cumulative S T (fun α => maxVariable q α.val) q i
    (fun α _ => maxVariable_le_variables q α.val) (fun α _ => maxVariable_le_variables q α.val) hc hcum

attribute [local instance] MvPolynomial.gradedAlgebra

theorem idealDegreeCard_add_hilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) (d : ℕ) :
    idealDegreeCard k q I d+quotientHilbert k q I hI d=Fintype.card (PolynomialDegreeIndex q d) := by
  rw [idealDegreeCard,quotientHilbert_eq_standard_card]
  simp_rw [standardExponent_iff_not_mem k q hmono]
  rw [Fintype.card_subtype_compl]
  have hle := Fintype.card_subtype_le (fun α : PolynomialDegreeIndex q d => MvPolynomial.monomial α.val (1:k)∈I)
  omega

theorem IsStronglyStable.binomial_degree_sum_le_lex_of_hilbert
    (I L : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hL : IsLex k q L)
    (hHomI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hHomL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (d i : ℕ) (hH : quotientHilbert k q I hHomI d=quotientHilbert k q L hHomL d) :
    degreeBinomialSum k q I d i≤degreeBinomialSum k q L d i := by
  have hci := idealDegreeCard_add_hilbert k q I hHomI hI.1 d
  have hcl := idealDegreeCard_add_hilbert k q L hHomL hL.1 d
  exact hI.binomial_degree_sum_le_lex k q I L hL d i (by omega)
end NSP14.Lex

