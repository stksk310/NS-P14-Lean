module
public import NSP14.NarrowFour.CoreWords
public import Mathlib.Data.Nat.Choose.Sum
public import NSP14.Endpoint.CoreLowDegrees
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.NarrowFour
variable (D : Endpoint.Data)

def IsSocleWord (a b : D.a) (p : ℕ×ℕ) : Prop :=
  ¬Standard D a b (p.1+1,p.2) ∧ ¬Standard D a b (p.1,p.2+1)

noncomputable def socleWords (a b : D.a) : Finset (ℕ×ℕ) :=
  (standardWords D a b).filter (IsSocleWord D a b)

@[simp] theorem mem_socleWords (a b : D.a) (p : ℕ×ℕ) :
    p∈socleWords D a b ↔ Standard D a b p ∧ IsSocleWord D a b p := by
  rw [socleWords,Finset.mem_filter,mem_standardWords]

theorem socle_condition_iff (hq : D.q=2) (p : D.CoreMinimalIndex) :
    (¬D.internalSurvives ((D.twoInternalEquiv hq).symm 0) p ∧
      ¬D.internalSurvives ((D.twoInternalEquiv hq).symm 1) p) ↔
      ∀ c : D.a, ¬D.internalSurvives c p := by
  constructor
  · intro h c
    have hc := D.twoInternalList_mem hq c
    have hc' : c=(D.twoInternalEquiv hq).symm 1 ∨ c=(D.twoInternalEquiv hq).symm 0 := by
      simpa only [Endpoint.Data.twoInternalList,List.mem_cons,List.not_mem_nil,or_false] using hc
    rcases hc' with rfl|rfl
    · exact h.2
    · exact h.1
  · intro h
    exact ⟨h _,h _⟩

theorem socle_word_iff (hq : D.q=2) (a b : D.a) (hab : OrderedPair D a b)
    (p : ↑(standardWords D a b)) :
    (¬D.internalSurvives ((D.twoInternalEquiv hq).symm 0) (standardWordEquiv D a b hab p) ∧
      ¬D.internalSurvives ((D.twoInternalEquiv hq).symm 1) (standardWordEquiv D a b hab p)) ↔
    IsSocleWord D a b p.val := by
  have hleft : D.internalSurvives a (standardWordEquiv D a b hab p) ↔
      Standard D a b (p.val.1+1,p.val.2) := by
    change D.CoreMinimal (word D a b p.val.1 p.val.2+D.coreGeneratorPoint (D.internalVariable a)) ↔ _
    rw [Standard,word_succ_fst,add_comm]
  have hright : D.internalSurvives b (standardWordEquiv D a b hab p) ↔
      Standard D a b (p.val.1,p.val.2+1) := by
    change D.CoreMinimal (word D a b p.val.1 p.val.2+D.coreGeneratorPoint (D.internalVariable b)) ↔ _
    rw [Standard,word_succ_snd,add_comm]
  rw [socle_condition_iff]
  constructor
  · intro h
    exact ⟨(not_congr hleft).mp (h a),(not_congr hright).mp (h b)⟩
  · intro h c
    rcases hab.2 c with rfl|rfl
    · exact (not_congr hleft).mpr h.1
    · exact (not_congr hright).mpr h.2

noncomputable def socleWordEquiv (hq : D.q=2) (a b : D.a) (hab : OrderedPair D a b) :
    ↑(socleWords D a b) ≃ D.InternalSocleIndex hq := by
  let e : ↑(socleWords D a b) ≃ {p : ↑(standardWords D a b) // IsSocleWord D a b p.val} := {
    toFun := fun p => ⟨⟨p.val,(mem_standardWords D a b p.val).mpr
      ((mem_socleWords D a b p.val).mp p.property).1⟩,
      ((mem_socleWords D a b p.val).mp p.property).2⟩
    invFun := fun p => ⟨p.val.val,(mem_socleWords D a b _).mpr
      ⟨(mem_standardWords D a b _).mp p.val.property,p.property⟩⟩
    left_inv := fun p => Subtype.ext rfl
    right_inv := fun p => Subtype.ext (Subtype.ext rfl) }
  exact e.trans (Equiv.subtypeEquiv (standardWordEquiv D a b hab)
    (fun p => (socle_word_iff D hq a b hab p).symm))

theorem sigma_card (k : Type) [Field k] (hq : D.q=2) (a b : D.a)
    (hab : OrderedPair D a b) : D.internalSigma k hq=(socleWords D a b).card := by
  rw [D.internalSigma_point_count k hq]
  rw [←Nat.card_congr (socleWordEquiv D hq a b hab),Nat.card_eq_fintype_card,Fintype.card_coe]

/-- Actual socle words form an antichain; each first coordinate is unique. -/
theorem socle_fst_injective (a b : D.a) :
    Function.Injective (fun p : ↑(socleWords D a b) => p.val.1) := by
  intro p q he
  apply Subtype.ext
  apply Prod.ext he
  by_contra hn
  have hp := (mem_socleWords D a b p.val).mp p.property
  have hq := (mem_socleWords D a b q.val).mp q.property
  rcases lt_or_gt_of_ne hn with hl|hl
  · exact hp.2.2 (standard_downward D a b q.val (p.val.1,p.val.2+1) hq.1 ⟨he.le,by omega⟩)
  · exact hq.2.2 (standard_downward D a b p.val (q.val.1,q.val.2+1) hp.1 ⟨he.symm.le,by omega⟩)

theorem socle_snd_injective (a b : D.a) :
    Function.Injective (fun p : ↑(socleWords D a b) => p.val.2) := by
  intro p q he
  apply Subtype.ext
  apply Prod.ext
  · by_contra hn
    have hp := (mem_socleWords D a b p.val).mp p.property
    have hq := (mem_socleWords D a b q.val).mp q.property
    rcases lt_or_gt_of_ne hn with hl|hl
    · exact hp.2.1 (standard_downward D a b q.val (p.val.1+1,p.val.2) hq.1 ⟨by omega,he.le⟩)
    · exact hq.2.1 (standard_downward D a b p.val (q.val.1+1,q.val.2) hp.1 ⟨by omega,he.symm.le⟩)
  · exact he

/-- Fewer than s+t socle points can lie strictly below one of the two
coordinates. This supplies the entire triangle, rather than just its size. -/
theorem socle_triangle (a b : D.a) (s t : ℕ)
    (hst : s+t<(socleWords D a b).card) : Standard D a b (s,t) := by
  let F := (socleWords D a b).filter (fun p => p.1<s)
  let G := (socleWords D a b).filter (fun p => p.2<t)
  have hF : F.card≤s := by
    let f : ↑F → Fin s := fun p => ⟨p.val.1,(Finset.mem_filter.mp p.property).2⟩
    have hi : Function.Injective f := by
      intro p q he
      apply Subtype.ext
      have hp := (Finset.mem_filter.mp p.property).1
      have hq := (Finset.mem_filter.mp q.property).1
      exact congrArg (fun z : ↑(socleWords D a b) => z.val) (socle_fst_injective D a b (a₁ := ⟨p.val,hp⟩)
        (a₂ := ⟨q.val,hq⟩) (congrArg Fin.val he))
    have h := Fintype.card_le_of_injective f hi
    simpa only [Fintype.card_coe,Fintype.card_fin] using h
  have hG : G.card≤t := by
    let f : ↑G → Fin t := fun p => ⟨p.val.2,(Finset.mem_filter.mp p.property).2⟩
    have hi : Function.Injective f := by
      intro p q he
      apply Subtype.ext
      have hp := (Finset.mem_filter.mp p.property).1
      have hq := (Finset.mem_filter.mp q.property).1
      exact congrArg (fun z : ↑(socleWords D a b) => z.val) (socle_snd_injective D a b (a₁ := ⟨p.val,hp⟩)
        (a₂ := ⟨q.val,hq⟩) (congrArg Fin.val he))
    have h := Fintype.card_le_of_injective f hi
    simpa only [Fintype.card_coe,Fintype.card_fin] using h
  by_contra hn
  have hsub : socleWords D a b ⊆ F∪G := by
    intro p hp
    have hmin := ((mem_socleWords D a b p).mp hp).1
    have hnot : p.1<s ∨ p.2<t := by
      by_contra! hh
      exact hn (standard_downward D a b p (s,t) hmin ⟨hh.1,hh.2⟩)
    rcases hnot with h|h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hp,h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hp,h⟩))
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le F G)
  omega


/-- The strict degree triangle has precisely the usual triangular cardinality. -/
theorem triangle_indices_card (n : ℕ) :
    Fintype.card (Σ s : Fin n,Fin (s.val+1))=(n+1).choose 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i+1) n]
  induction n with
  | zero => decide
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,Nat.choose_succ_succ (n+1) 1]
    simp only [Nat.choose_one_right,add_comm]

theorem socle_triangle_card (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) :
    (D.internalSigma k hq+1).choose 2≤D.coreP k := by
  rw [sigma_card D k hq a b hab,coreP_card D k a b hab]
  let n := (socleWords D a b).card
  let f : (Σ s : Fin n,Fin (s.val+1)) → ↑(standardWords D a b) := fun p =>
    ⟨(p.1.val-p.2.val,p.2.val),(mem_standardWords D a b _).mpr
      (socle_triangle D a b _ _ (by have := p.1.isLt; have := p.2.isLt; omega))⟩
  have hi : Function.Injective f := by
    rintro ⟨s,t⟩ ⟨x,y⟩ he
    have ht := congrArg (fun p : ↑(standardWords D a b) => p.val.2) he
    have hs := congrArg (fun p : ↑(standardWords D a b) => p.val.1) he
    change t.val=y.val at ht
    change s.val-t.val=x.val-y.val at hs
    have heS : s=x := Fin.ext (by have := t.isLt; have := y.isLt; omega)
    subst x
    have heT : t=y := Fin.ext ht
    subst y
    rfl
  have hc := Fintype.card_le_of_injective f hi
  simpa only [triangle_indices_card,Fintype.card_coe] using hc

theorem standard_zero (a b : D.a) : Standard D a b (0,0) := by
  simpa only [Standard,word,zero_nsmul,add_zero] using D.coreZero_minimal

/-- Full inclusion of the socle triangle in the actual standard-word set. -/
theorem standard_of_degree_lt_sigma (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (s t : ℕ)
    (hst : s+t≤D.internalSigma k hq-1) : Standard D a b (s,t) := by
  by_cases hz : D.internalSigma k hq=0
  · have hs : s=0 := by omega
    have ht : t=0 := by omega
    subst s; subst t
    exact standard_zero D a b
  · apply socle_triangle D a b s t
    rw [←sigma_card D k hq a b hab]
    omega

end NSP14.NarrowFour
