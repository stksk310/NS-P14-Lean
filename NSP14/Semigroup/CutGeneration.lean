module

public import NSP14.Semigroup.CutAction
public import NSP14.Semigroup.TowerIntervals
public import NSP14.Green.FormProducts

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type*) [Field k]

noncomputable def headFormMap (C : S.LinearCutData k) (n : ℕ) :
    (Fin S.actualCutRank → S.headDegree k n) →ₗ[k] S.headDegree k (n+1) where
  toFun b := ⟨∑ i, (C.forms i).val * (b i).val, by
    apply Submodule.sum_mem
    intro i _
    simpa only [Nat.add_comm 1 n] using
      S.headDegree_mul_mem k (n:=1) (p:=n) (C.forms i).property (b i).property⟩
  map_add' b c := by apply Subtype.ext; simp [mul_add,Finset.sum_add_distrib]
  map_smul' r b := by apply Subtype.ext; simp [mul_smul_comm,Finset.smul_sum]

theorem headFormMap_surjective (C : S.LinearCutData k) (n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (S.headFormMap k C n) := by
  have hquad : Function.Surjective (NSP14.Green.formProductMap (S.quadraticProduct k) C.forms) := by
    apply NSP14.Green.formProductMap_surjective
    simpa only [NSP14.Green.flagSpan_full] using C.quadratic_span
  let U := (S.headFormMap k C n).range.map (S.headDegree k (n+1)).subtype
  have hle : S.headDegree k (n+1) ≤ U := by
    intro a ha
    have hs : ∀ h ∈ (S.headQuotientEquiv k a).support, S.order h.val.val = n+1 :=
      (Finsupp.mem_supported k _).1 ((S.mem_headDegree_coordinates k (n+1) a).1 ha)
    rw [← S.head_expansion k a,Finsupp.sum]
    apply U.sum_mem
    intro h hh
    apply U.smul_mem
    have hord := hs h hh
    obtain ⟨u,v,he,hu,hv⟩ := S.order_live_split h.val 2 (by omega)
    have hvn : S.order v.val = n-1 := by omega
    obtain ⟨b,hb⟩ := hquad ⟨S.headMonomial k u,S.headMonomial_mem_degree k u 2 hu⟩
    let c : Fin S.actualCutRank → S.headDegree k n := fun i =>
      ⟨(b i).val * S.headMonomial k v,by
        have ht := S.headDegree_mul_mem k (n:=1) (p:=n-1) (b i).property
          (S.headMonomial_mem_degree k v (n-1) hvn)
        simpa only [show 1+(n-1)=n by omega] using ht⟩
    refine ⟨S.headFormMap k C n c,⟨c,rfl⟩,?_⟩
    have hb' := congrArg Subtype.val hb
    change (∑ i, S.quadraticProduct k (C.forms i) (b i)).val = S.headMonomial k u at hb'
    simp only [Submodule.coe_sum] at hb'
    change (∑ i, (C.forms i).val * (b i).val) = S.headMonomial k u at hb'
    change (∑ i, (C.forms i).val * ((b i).val * S.headMonomial k v)) = _
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul,hb']
    ·
      have hlive : S.order (u.val+v.val) = S.order u.val + S.order v.val := by
        have heval : h.val.val = u.val+v.val := congrArg Subtype.val he
        rw [← heval,hord,hu,hvn]
        omega
      rw [S.headMonomial_mul_live k u v hlive,← he,S.headMonomial_eq_basis]
  rw [← LinearMap.range_eq_top]
  apply top_unique
  intro a _
  obtain ⟨b,hb,he⟩ := hle a.property
  exact (Subtype.ext he : b=a) ▸ hb

noncomputable def stageFormMap (C : S.LinearCutData k) (s n : ℕ) :
    (Fin S.actualCutRank → S.towerStageDegree k s n) →ₗ[k] S.towerStageDegree k s (n+1) where
  toFun b := ⟨∑ i, Ideal.Quotient.mk _ (C.forms i).val * (b i).val,by
    apply Submodule.sum_mem
    intro i _
    obtain ⟨a,ha,he⟩ := (b i).property
    refine ⟨(C.forms i).val*a,?_,?_⟩
    · change (C.forms i).val*a ∈ S.headDegree k (n+1)
      change a ∈ S.headDegree k n at ha
      simpa only [Nat.add_comm 1 n] using
        S.headDegree_mul_mem k (n:=1) (p:=n) (C.forms i).property ha
    · change Ideal.Quotient.mk _ ((C.forms i).val*a) = _
      change Ideal.Quotient.mk _ a = (b i).val at he
      rw [map_mul,he]⟩
  map_add' b c := by apply Subtype.ext; simp [mul_add,Finset.sum_add_distrib]
  map_smul' r b := by apply Subtype.ext; simp [mul_smul_comm,Finset.smul_sum]

theorem stageFormMap_surjective (C : S.LinearCutData k) (s n : ℕ) (hn : 1 ≤ n) :
    Function.Surjective (S.stageFormMap k C s n) := by
  intro a
  obtain ⟨v,hv,he⟩ := a.property
  obtain ⟨b,hb⟩ := S.headFormMap_surjective k C n hn ⟨v,hv⟩
  let c : Fin S.actualCutRank → S.towerStageDegree k s n := fun i =>
    ⟨Ideal.Quotient.mk _ (b i).val,(b i).val,(b i).property,rfl⟩
  refine ⟨c,Subtype.ext ?_⟩
  have hb' := congrArg Subtype.val hb
  change (∑ i, Ideal.Quotient.mk _ (C.forms i).val * Ideal.Quotient.mk _ (b i).val) = a.val
  change (∑ i, (C.forms i).val * (b i).val) = v at hb'
  change Ideal.Quotient.mk _ v = a.val at he
  calc
    _ = Ideal.Quotient.mk _ (∑ i, (C.forms i).val * (b i).val) := by rw [map_sum]; simp only [map_mul]
    _ = _ := by rw [hb',he]

theorem stageDegree_step_bound (C : S.LinearCutData k) (s n : ℕ) (hn : 1 ≤ n) :
    Module.finrank k (S.towerStageDegree k s (n+1)) ≤
      S.actualCutRank * Module.finrank k (S.towerStageDegree k s n) := by
  have h := LinearMap.finrank_le_finrank_of_surjective (S.stageFormMap_surjective k C s n hn)
  simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h

theorem towerResource_head_linear (C : S.LinearCutData k) :
    S.towerResource k 1 ≤ S.actualCutRank * S.deficit := by
  rw [← S.towerResource_zero k, towerResource, towerResource,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s hs
  simpa only [Nat.add_zero] using S.stageDegree_step_bound k C s s (by
    have := (Finset.mem_Icc.mp hs).1; omega)

end NSP14.NumericalSemigroup
