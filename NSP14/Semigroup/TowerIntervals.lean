module

public import NSP14.Semigroup.TowerCoordinates

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

abbrev TowerIndex (t : ℕ) :=
  Σ s : ↥(Finset.Icc 2 S.qTopDegree), S.StageDegreeExponent s.val (s.val + t)

def HeadContributes (t : ℕ) (h : S.HeadExponent) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ s ≤ S.qTopDegree ∧ S.StageAlive s h ∧ S.order h.val.val = s + t

abbrev ContributingHead (t : ℕ) := {h : S.HeadExponent // S.HeadContributes t h}

noncomputable instance towerIndexFintype (t : ℕ) : Fintype (S.TowerIndex t) := by
  classical
  infer_instance

noncomputable instance contributingHeadFintype (t : ℕ) : Fintype (S.ContributingHead t) := by
  classical
  infer_instance

noncomputable def towerIndexHeadEquiv (t : ℕ) : S.TowerIndex t ≃ S.ContributingHead t :=
  Equiv.ofBijective (fun a => ⟨a.2.val.val, a.1.val,
    (Finset.mem_Icc.mp a.1.property).1,(Finset.mem_Icc.mp a.1.property).2,a.2.val.property,a.2.property⟩) (by
    constructor
    · rintro ⟨s,h⟩ ⟨u,j⟩ he
      have hv : h.val.val = j.val.val := congrArg (fun a : S.ContributingHead t => a.val) he
      have ho := congrArg (fun a : S.HeadExponent => S.order a.val.val) hv
      rw [h.property,j.property] at ho
      have hs : s = u := Subtype.ext (by omega)
      subst u
      have hh : h = j := Subtype.ext (Subtype.ext hv)
      subst j
      rfl
    · intro h
      obtain ⟨s,hs,hν,ha,ho⟩ := h.property
      exact ⟨⟨⟨s,Finset.mem_Icc.mpr ⟨hs,hν⟩⟩,⟨⟨h.val,ha⟩,ho⟩⟩,Subtype.ext rfl⟩)

variable (k : Type*) [Field k]

/-- H counts exactly the surviving head intervals, with no multiplicities
from two different stages for the same head at the same t. -/
theorem towerResource_card (t : ℕ) : S.towerResource k t = Fintype.card (S.ContributingHead t) := by
  rw [← Fintype.card_congr (S.towerIndexHeadEquiv t),Fintype.card_sigma]
  unfold towerResource
  simp only [S.towerStageDegree_finrank]
  exact (Finset.sum_coe_sort _ _).symm

theorem towerResource_field_independent (L : Type*) [Field L] (t : ℕ) :
    S.towerResource k t = S.towerResource L t := by
  rw [S.towerResource_card k,S.towerResource_card L]

omit [Field k] in
/-- The interval belonging to an actual Apéry head. -/
theorem headContributes_apery (t : ℕ) (h : S.HeadExponent) (ha : h.val.val ∈ S.aperySet) :
    S.HeadContributes t h ↔ t + 2 ≤ S.order h.val.val := by
  constructor
  · rintro ⟨s,hs,_,_,ho⟩
    omega
  · intro ht
    have hν : S.order h.val.val ≤ S.qTopDegree :=
      S.apery_order_le_top (⟨h.val,ha⟩ : S.AperyExponent)
    refine ⟨S.order h.val.val-t,by omega,by omega,?_,by omega⟩
    change ¬(h.val.val ∉ S.aperySet ∧ _)
    exact fun hn => hn.1 ha

omit [Field k] in
/-- A terminal of degree p and jump d contributes exactly [p,p+d-2]. -/
theorem headContributes_nonapery (t : ℕ) (h : S.HeadExponent) (ha : h.val.val ∉ S.aperySet) :
    S.HeadContributes t h ↔
      S.order (h.val.val-S.multiplicity) ≤ t ∧ t + 2 ≤ S.order h.val.val := by
  have hterm := S.head_sub_terminal (⟨h.property,ha⟩ : S.NonAperyHead h.val.val)
  have hp := S.order_pos hterm.1 (S.terminal_pos hterm)
  have hj := S.terminal_jump hterm
  have hν := S.terminal_jump_upper hterm
  have hdegree : S.order h.val.val = S.order (h.val.val-S.multiplicity) +
      S.jump (h.val.val-S.multiplicity) := by
    obtain ⟨x,hx,he⟩ := S.head_predecessor (⟨h.property,ha⟩ : S.NonAperyHead h.val.val)
    have he' : h.val.val-S.multiplicity+S.multiplicity = h.val.val := by omega
    have ho := S.order_add_multiplicity hterm.1
    unfold jump
    rw [he'] at ho ⊢
    omega
  constructor
  · rintro ⟨s,hs,_,hal,ho⟩
    have hle : s ≤ S.jump (h.val.val-S.multiplicity) := by
      change ¬(h.val.val ∉ S.aperySet ∧ S.jump (h.val.val-S.multiplicity) ≤ s-1) at hal
      have hnot : ¬S.jump (h.val.val-S.multiplicity) ≤ s-1 := fun hh => hal ⟨ha,hh⟩
      omega
    omega
  · rintro ⟨hpt,ht⟩
    refine ⟨S.order h.val.val-t,by omega,by omega,?_,by omega⟩
    change ¬(h.val.val ∉ S.aperySet ∧ S.jump (h.val.val-S.multiplicity) ≤ (S.order h.val.val-t)-1)
    rintro ⟨_,hh⟩
    omega

end NSP14.NumericalSemigroup
