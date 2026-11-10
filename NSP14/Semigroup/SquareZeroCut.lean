module

public import NSP14.Semigroup.ActualGreen
public import NSP14.Green.ExtendIndependent

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [Field k]

/-- Killing actual degree two kills every higher actual degree, by a live
factorization with a degree-two prefix. -/
theorem highDegree_mem_of_degree_two (I : Ideal (S.HeadAlgebra k))
    (hI : ∀ a ∈ S.headDegree k 2, a ∈ I) (n : ℕ) (hn : 2 ≤ n)
    (a : S.HeadAlgebra k) (ha : a ∈ S.headDegree k n) : a ∈ I := by
  have hs : ∀ h ∈ (S.headQuotientEquiv k a).support, S.order h.val.val = n :=
    (Finsupp.mem_supported k _).1 ((S.mem_headDegree_coordinates k n a).1 ha)
  rw [← S.head_expansion k a,Finsupp.sum]
  apply (I.restrictScalars k).sum_mem
  intro h hh
  apply (I.restrictScalars k).smul_mem
  have hord := hs h hh
  obtain ⟨u,v,he,hu,hv⟩ := S.order_live_split h.val 2 (by omega)
  have hU := hI (S.headMonomial k u) (S.headMonomial_mem_degree k u 2 hu)
  have hprod := I.mul_mem_right (S.headMonomial k v) hU
  have hlive : S.order (u.val+v.val) = S.order u.val + S.order v.val := by
    have heval : h.val.val = u.val+v.val := congrArg Subtype.val he
    rw [← heval,hord,hu,hv,hord]
    omega
  rw [S.headMonomial_mul_live k u v hlive, ← he, S.headMonomial_eq_basis] at hprod
  exact hprod

structure LinearCutData where
  forms : Fin S.actualCutRank → S.headDegree k 1
  independent : LinearIndependent k forms
  quadratic_span : NSP14.Green.cutImage (S.quadraticProduct k)
    (NSP14.Green.flagSpan (k := k) forms S.actualCutRank) = ⊤

theorem LinearCutData.quadratic_mem (C : S.LinearCutData k)
    (a : S.HeadAlgebra k) (ha : a ∈ S.headDegree k 2) :
    a ∈ S.linearCutIdeal k C.forms S.actualCutRank := by
  apply S.quadraticCutImage_mem_cutIdeal k C.forms S.actualCutRank ⟨a,ha⟩
  rw [C.quadratic_span]
  trivial

theorem LinearCutData.high_mem (C : S.LinearCutData k) (n : ℕ) (hn : 2 ≤ n)
    (a : S.HeadAlgebra k) (ha : a ∈ S.headDegree k n) :
    a ∈ S.linearCutIdeal k C.forms S.actualCutRank :=
  S.highDegree_mem_of_degree_two k _ C.quadratic_mem n hn a ha

/-- One independent square-zero cut exists in the prescribed rank. It is
constructed from the proved Green flag, including padding when p<2. -/
theorem linearCutData_nonempty [Infinite k] (he : 3 ≤ S.embeddingDimension) :
    Nonempty (S.LinearCutData k) := by
  let a := (S.degreeSet 2).card
  let p := NSP14.Ordinary.quadraticIndex a
  have hdim : p ≤ Module.finrank k (S.headDegree k 1) := by
    rw [S.headDegree_one_finrank]
    apply NSP14.Ordinary.quadraticIndex_le_of_bound
    unfold NSP14.Ordinary.quadraticTriangular
    rw [Nat.sub_add_cancel (show 1 ≤ S.embeddingDimension from S.embeddingDimension_pos)]
    exact S.degree_two_card_le_quadratic
  have hcap : Module.finrank k (S.headDegree k 2) ≤
      (p + 1).choose 2 + (a - NSP14.Ordinary.quadraticTriangular p) := by
    rw [S.headDegree_two_finrank]
    have h := NSP14.Ordinary.quadraticIndex_lower a
    change a ≤ NSP14.Ordinary.quadraticTriangular p + (a - NSP14.Ordinary.quadraticTriangular p)
    omega
  obtain ⟨c,hc,hcut⟩ := NSP14.Green.exists_quadratic_zero_cut (S.quadraticProduct k)
    (S.quadraticProduct_symmetric k) (S.quadraticProduct_spans k) p
    (a - NSP14.Ordinary.quadraticTriangular p) (NSP14.Ordinary.quadratic_decomposition a).2 hdim hcap
  have hp : p ≤ S.actualCutRank := le_max_right 2 p
  have hr : S.actualCutRank ≤ Module.finrank k (S.headDegree k 1) := by
    rw [S.headDegree_one_finrank]
    exact S.actualCutRank_le he
  obtain ⟨d,hd,hspan⟩ := NSP14.Green.extend_independent c hc hp hr
  refine ⟨⟨d,hd,?_⟩⟩
  have hmono := NSP14.Green.cutImage_mono (S.quadraticProduct k) hspan
  rw [NSP14.Green.flagSpan_full] at hcut
  rw [hcut] at hmono
  rw [NSP14.Green.flagSpan_full]
  exact top_unique hmono

/-- The cut is selected once, then reused by all following constructions. -/
noncomputable def fixedLinearCut [Infinite k] (he : 3 ≤ S.embeddingDimension) : S.LinearCutData k :=
  (S.linearCutData_nonempty k he).some

end NSP14.NumericalSemigroup
