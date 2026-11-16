module
public import NSP14.Semigroup.TowerCoordinates
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type*) [Field k]

noncomputable def highSpace (n : ℕ) : Submodule k (S.HeadAlgebra k) :=
  (Finsupp.supported k k {h : S.HeadExponent | n ≤ S.order h.val.val}).comap
    (S.headQuotientEquiv k).toLinearMap

theorem headDegree_le_highSpace (n d : ℕ) (hd : n ≤ d) : S.headDegree k d ≤ S.highSpace k n := by
  intro a ha
  change S.headQuotientEquiv k a ∈ Finsupp.supported k k _
  rw [Finsupp.mem_supported']
  intro h hh
  apply (Finsupp.mem_supported' k _).1 ((S.mem_headDegree_coordinates k d a).1 ha) h
  intro he
  change S.order h.val.val=d at he
  apply hh
  change n ≤ S.order h.val.val
  exact he.symm ▸ hd

theorem headBasis_mem_highSpace (n : ℕ) (h : S.HeadExponent) (hh : n ≤ S.order h.val.val) :
    S.headBasis k h ∈ S.highSpace k n := by
  apply S.headDegree_le_highSpace k n (S.order h.val.val) hh
  rw [← S.headMonomial_eq_basis k h]
  exact S.headMonomial_mem_degree k h.val (S.order h.val.val) rfl

theorem highSpace_mul (n : ℕ) (r a : S.HeadAlgebra k) (ha : a ∈ S.highSpace k n) :
    r*a ∈ S.highSpace k n := by
  have hs : ∀ h ∈ (S.headQuotientEquiv k a).support,n ≤ S.order h.val.val :=
    (Finsupp.mem_supported k _).1 ha
  rw [← S.head_expansion k r,Finsupp.sum,Finset.sum_mul]
  apply (S.highSpace k n).sum_mem
  intro g _
  rw [← S.head_expansion k a,Finsupp.sum,Finset.mul_sum]
  apply (S.highSpace k n).sum_mem
  intro h hh
  rw [smul_mul_assoc]
  apply (S.highSpace k n).smul_mem
  rw [mul_smul_comm]
  apply (S.highSpace k n).smul_mem
  change S.headQuotientEquiv k (S.headBasis k g*S.headBasis k h) ∈ Finsupp.supported k k _
  rw [Finsupp.mem_supported']
  intro u hu
  rw [← S.headMonomial_eq_basis k g,← S.headMonomial_eq_basis k h,S.head_product_coordinate]
  split_ifs with hl
  · have hne : g.val+h.val ≠ u.val := by
      intro he
      have heval : g.val.val+h.val.val=u.val.val := congrArg Subtype.val he
      change ¬n ≤ S.order u.val.val at hu
      have hn := hs h hh
      rw [heval] at hl
      omega
    simp [hne]
  · rfl

noncomputable def highIdeal (n : ℕ) : Ideal (S.HeadAlgebra k) where
  carrier := S.highSpace k n
  zero_mem' := (S.highSpace k n).zero_mem
  add_mem' := (S.highSpace k n).add_mem
  smul_mem' r a ha := S.highSpace_mul k n r a ha

theorem highIdeal_antitone : Antitone (S.highIdeal k) := by
  intro n d hnd a ha
  change S.headQuotientEquiv k a ∈ Finsupp.supported k k _ at ha ⊢
  rw [Finsupp.mem_supported'] at ha ⊢
  exact fun h hh => ha h (fun hd => hh (hnd.trans hd))

/-- Actual truncations inside the actual quotient U_s. -/
noncomputable def towerHighIdeal (s n : ℕ) : Ideal (S.TowerStage k s) :=
  (S.highIdeal k n).map (Ideal.Quotient.mk (S.jumpIdeal k (s-1)))

abbrev TowerX (s : ℕ) := ↥(S.towerHighIdeal k s s)
abbrev TowerM (s : ℕ) := ↥(S.towerHighIdeal k s (s+1))

/-- The degree-n piece maps into the degree≥n actual truncation. -/
theorem towerStageDegree_le_high (s n d : ℕ) (hd : n ≤ d) :
    S.towerStageDegree k s d ≤ (S.towerHighIdeal k s n).restrictScalars k := by
  rintro a ⟨b,hb,rfl⟩
  exact Ideal.mem_map_of_mem _ (S.headDegree_le_highSpace k n d hd hb)

theorem highIdeal_top_le_nonApery : S.highIdeal k (S.qTopDegree+1) ≤ S.nonAperyIdeal k := by
  intro a ha
  apply (S.mem_nonAperySpace k a).2
  intro h hh
  have hν : S.order h.val.val ≤ S.qTopDegree := S.apery_order_le_top ⟨h.val,hh⟩
  exact (Finsupp.mem_supported' k _).1 ha h (by
    change ¬S.qTopDegree+1 ≤ S.order h.val.val
    omega)

theorem towerX_top_zero : S.towerHighIdeal k (S.qTopDegree+1) (S.qTopDegree+1) = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨b,hb,rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ha
  change Ideal.Quotient.mk _ b=0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change b ∈ S.jumpIdeal k S.qTopDegree
  rw [S.jumpIdeal_top]
  exact S.highIdeal_top_le_nonApery k hb

end NSP14.NumericalSemigroup
