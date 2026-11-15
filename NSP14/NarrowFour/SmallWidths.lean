module
public import NSP14.NarrowFour.FirstLarge
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical
open NSP14.Homological
namespace NSP14.NarrowFour
variable (D : Endpoint.Data)

theorem pair_gcd (a b : D.a) (hab : OrderedPair D a b) :
    Nat.gcd (Nat.gcd a.val b.val) D.u=1 := by
  have he : D.a={a.val,b.val} := by
    ext x
    constructor
    · intro hx
      rcases hab.2 ⟨x,hx⟩ with h|h
      · exact Finset.mem_insert.mpr (Or.inl (congrArg (fun z : D.a => z.val) h))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (congrArg (fun z : D.a => z.val) h)))
    · intro hx
      rcases Finset.mem_insert.mp hx with hx|hx
      · rw [hx];exact a.property
      · rw [Finset.mem_singleton.mp hx];exact b.property
  have h := D.offsets_coprime
  simpa [he,gcd_eq_nat_gcd] using h

theorem sigma_le_forbidden (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (r w : ℕ) (hf : ¬Standard D a b (r,w)) :
    D.internalSigma k hq ≤ r+w := by
  by_contra hn
  exact hf (standard_of_degree_lt_sigma D k hq a b hab r w (by omega))

def boundedWords (h S T r w : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.range S).product (Finset.range T)).filter
    (fun p => (p.1=0 ∨ p.2=0 ∨ p.1+p.2 ≤ h) ∧ ¬(r ≤ p.1 ∧ w ≤ p.2))

theorem coreP_boundedWords (k : Type) [Field k] (_hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (S T r w : ℕ)
    (hS : ¬Standard D a b (S,0)) (hT : ¬Standard D a b (0,T))
    (hf : ¬Standard D a b (r,w)) :
    D.coreP k ≤ (boundedWords (D.u/2) S T r w).card := by
  rw [coreP_card D k a b hab]
  apply Finset.card_le_card
  intro p hp
  have hs := (mem_standardWords D a b p).mp hp
  have hne : a≠b := fun h => (ne_of_lt hab.1) (congrArg (fun z : D.a => z.val) h)
  have h1 : p.1<S := by
    by_contra hn
    exact hS (standard_downward D a b p (S,0) hs ⟨by omega,Nat.zero_le _⟩)
  have h2 : p.2<T := by
    by_contra hn
    exact hT (standard_downward D a b p (0,T) hs ⟨Nat.zero_le _,by omega⟩)
  rw [boundedWords,Finset.mem_filter]
  refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr h1,Finset.mem_range.mpr h2⟩,?_,?_⟩
  · by_cases hz : p.1=0
    · exact Or.inl hz
    by_cases ht : p.2=0
    · exact Or.inr (Or.inl ht)
    have hm := standard_mixed_bound D a b hne p.1 p.2 (by omega) (by omega) hs
    exact Or.inr (Or.inr (by omega))
  · intro hr
    exact hf (standard_downward D a b p (r,w) hs hr)

theorem actualR_add_volume (k : Type) [Field k] : D.actualR k+D.u ≤ D.wordVolume := by
  have := D.actualR_le_volume k
  have := D.wordVolume_ge_u
  omega

/-- Reusable transfer from actual word-length control to the original height coordinate. -/
theorem coreHeight_of_length (_hq : D.q=2) (a b : D.a) (hab : OrderedPair D a b)
    (H : ℕ) (hwords : ∀ s t, Standard D a b (s,t) → s+t ≤ H+1) : D.coreHeight ≤ H := by
  unfold Endpoint.Data.coreHeight
  apply Finset.sup_le
  intro r _
  apply Finset.sup_le
  intro c hc
  have hc' := (D.mem_minimalPoints r c).mp hc
  by_cases hr : r.val=0
  · have hr' : r=⟨0,D.u_pos⟩ := Fin.ext hr
    subst r
    rw [D.minimalFiber_zero c hc']
    exact Nat.zero_le _
  · let p : D.CoreMinimalIndex := ⟨⟨D.decodeCoordinate (r,c),hc'.prop⟩,by
      change Minimal (·∈D.coreFiber (D.coreCoordinates _).1) (D.coreCoordinates _).2
      rw [D.coreCoordinates_decode]
      exact hc'⟩
    obtain ⟨s,t,he⟩ := minimal_representation D a b hab p
    have hstd : Standard D a b (s,t) := by
      change D.CoreMinimal (word D a b s t)
      rw [←he]
      exact p.property
    have hlen := hwords s t hstd
    have hd := congrArg D.coreDegree he
    rw [word_degree] at hd
    change c.1+c.2+D.epsilon r=s+t at hd
    have heps : D.epsilon r=1 := by simp only [Endpoint.Data.epsilon,ite_eq_right hr]
    rw [heps] at hd
    omega


theorem strip_6_1_5 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=6) (ha : a.val=1) (hb : b.val=5) :
    D.coreP k ≤ 9 ∧ D.internalSigma k hq ≤ 2 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 16 := by
  have hS : ¬Standard D a b (5,0) := by
    apply relation_forbidden D a b 5 0 0 1 4 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,5) := by
    apply relation_forbidden D a b 0 5 1 0 0 4 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (1,1) := by
    apply relation_forbidden D a b 1 1 0 0 1 1 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 5 5 1 1 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 9 at hp
  have hs : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 1 1 hf
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 10 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_7_1_4 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=7) (ha : a.val=1) (hb : b.val=4) :
    D.coreP k ≤ 7 ∧ D.internalSigma k hq ≤ 2 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 16 := by
  have hS : ¬Standard D a b (4,0) := by
    apply relation_forbidden D a b 4 0 0 1 3 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,2) := by
    apply relation_forbidden D a b 0 2 1 0 0 1 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (3,1) := by
    apply relation_forbidden D a b 3 1 0 0 3 1 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 4 2 3 1 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 7 at hp
  have hs : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 0 2 hT
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 13 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_7_2_5 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=7) (ha : a.val=2) (hb : b.val=5) :
    D.coreP k ≤ 9 ∧ D.internalSigma k hq ≤ 2 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 18 := by
  have hS : ¬Standard D a b (5,0) := by
    apply relation_forbidden D a b 5 0 0 2 3 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,5) := by
    apply relation_forbidden D a b 0 5 2 0 0 3 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (1,1) := by
    apply relation_forbidden D a b 1 1 0 0 1 1 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 5 5 1 1 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 9 at hp
  have hs : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 1 1 hf
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 13 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_7_3_6 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=7) (ha : a.val=3) (hb : b.val=6) :
    D.coreP k ≤ 7 ∧ D.internalSigma k hq ≤ 2 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 16 := by
  have hS : ¬Standard D a b (2,0) := by
    apply relation_forbidden D a b 2 0 0 1 1 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,4) := by
    apply relation_forbidden D a b 0 4 1 0 0 3 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (1,3) := by
    apply relation_forbidden D a b 1 3 0 0 1 3 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 2 4 1 3 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 7 at hp
  have hs : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 2 0 hS
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 13 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_8_1_5 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=8) (ha : a.val=1) (hb : b.val=5) :
    D.coreP k ≤ 14 ∧ D.internalSigma k hq ≤ 4 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 28 := by
  have hS : ¬Standard D a b (5,0) := by
    apply relation_forbidden D a b 5 0 0 1 4 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,5) := by
    apply relation_forbidden D a b 0 5 1 0 1 3 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (3,1) := by
    apply relation_forbidden D a b 3 1 0 0 3 1 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 5 5 3 1 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 14 at hp
  have hs : D.internalSigma k hq ≤ 4 := sigma_le_forbidden D k hq a b hab 3 1 hf
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_8_3_7 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=8) (ha : a.val=3) (hb : b.val=7) :
    D.coreP k ≤ 14 ∧ D.internalSigma k hq ≤ 4 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 28 := by
  have hS : ¬Standard D a b (5,0) := by
    apply relation_forbidden D a b 5 0 0 1 3 1 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,5) := by
    apply relation_forbidden D a b 0 5 1 0 0 4 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (1,3) := by
    apply relation_forbidden D a b 1 3 0 0 1 3 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 5 5 1 3 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 14 at hp
  have hs : D.internalSigma k hq ≤ 4 := sigma_le_forbidden D k hq a b hab 1 3 hf
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_8_1_4 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=8) (ha : a.val=1) (hb : b.val=4) :
    D.coreP k ≤ 8 ∧ D.internalSigma k hq ≤ 2 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 20 := by
  have hS : ¬Standard D a b (4,0) := by
    apply relation_forbidden D a b 4 0 0 1 3 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,2) := by
    apply relation_forbidden D a b 0 2 0 0 1 1 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (4,1) := by
    apply relation_forbidden D a b 4 1 0 0 4 1 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 4 2 4 1 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 8 at hp
  have hs : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 0 2 hT
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_8_2_5 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=8) (ha : a.val=2) (hb : b.val=5) :
    D.coreP k ≤ 9 ∧ D.internalSigma k hq ≤ 2 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 21 := by
  have hS : ¬Standard D a b (5,0) := by
    apply relation_forbidden D a b 5 0 0 2 3 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,2) := by
    apply relation_forbidden D a b 0 2 1 0 0 1 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (3,2) := by
    apply relation_forbidden D a b 3 2 0 0 3 2 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 5 2 3 2 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 9 at hp
  have hs : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 0 2 hT
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_8_3_6 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=8) (ha : a.val=3) (hb : b.val=6) :
    D.coreP k ≤ 9 ∧ D.internalSigma k hq ≤ 2 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 21 := by
  have hS : ¬Standard D a b (2,0) := by
    apply relation_forbidden D a b 2 0 0 1 1 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,5) := by
    apply relation_forbidden D a b 0 5 2 0 0 3 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (2,3) := by
    apply relation_forbidden D a b 2 3 0 0 2 3 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 2 5 2 3 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 9 at hp
  have hs : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 2 0 hS
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_8_4_7 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=8) (ha : a.val=4) (hb : b.val=7) :
    D.coreP k ≤ 8 ∧ D.internalSigma k hq ≤ 2 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 20 := by
  have hS : ¬Standard D a b (2,0) := by
    apply relation_forbidden D a b 2 0 0 0 1 1 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,4) := by
    apply relation_forbidden D a b 0 4 1 0 0 3 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (1,4) := by
    apply relation_forbidden D a b 1 4 0 0 1 4 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 2 4 1 4 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 8 at hp
  have hs : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 2 0 hS
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_8_1_3 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=8) (ha : a.val=1) (hb : b.val=3) :
    D.coreP k ≤ 14 ∧ D.internalSigma k hq ≤ 3 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 27 := by
  have hS : ¬Standard D a b (3,0) := by
    apply relation_forbidden D a b 3 0 0 1 2 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,7) := by
    apply relation_forbidden D a b 0 7 5 0 0 2 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (5,1) := by
    apply relation_forbidden D a b 5 1 0 0 5 1 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 3 7 5 1 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 14 at hp
  have hs : D.internalSigma k hq ≤ 3 := sigma_le_forbidden D k hq a b hab 3 0 hS
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_8_3_5 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=8) (ha : a.val=3) (hb : b.val=5) :
    D.coreP k ≤ 9 ∧ D.internalSigma k hq ≤ 2 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 21 := by
  have hS : ¬Standard D a b (5,0) := by
    apply relation_forbidden D a b 5 0 0 3 2 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,5) := by
    apply relation_forbidden D a b 0 5 3 0 0 2 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (1,1) := by
    apply relation_forbidden D a b 1 1 0 0 1 1 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 5 5 1 1 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 9 at hp
  have hs : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 1 1 hf
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩
theorem strip_8_5_7 (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u=8) (ha : a.val=5) (hb : b.val=7) :
    D.coreP k ≤ 14 ∧ D.internalSigma k hq ≤ 3 ∧
      totalBetti k D.Variables (D.fullG k) 1 ≤ 27 := by
  have hS : ¬Standard D a b (7,0) := by
    apply relation_forbidden D a b 7 0 0 5 2 0 <;> norm_num [hu,ha,hb]
  have hT : ¬Standard D a b (0,3) := by
    apply relation_forbidden D a b 0 3 1 0 0 2 <;> norm_num [hu,ha,hb]
  have hf : ¬Standard D a b (1,5) := by
    apply relation_forbidden D a b 1 5 0 0 1 5 <;> norm_num [hu,ha,hb]
  have hp := coreP_boundedWords D k hq a b hab 7 3 1 5 hS hT hf
  rw [hu] at hp
  change D.coreP k ≤ 14 at hp
  have hs : D.internalSigma k hq ≤ 3 := sigma_le_forbidden D k hq a b hab 0 3 hT
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hfirst := D.actual_two_row_one k hq
  exact ⟨hp,hs,by omega⟩



theorem actual_first_7 (k : Type) [Field k] (hq : D.q=2) (hu : D.u=7) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ 22 := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  have ha := D.a_pos _ a.property
  have hb := D.a_lt _ b.property
  have hab' := hab.1
  have hg := pair_gcd D a b hab
  let κ := D.u-b.val+a.val
  have hklo : 2 ≤ κ := by dsimp [κ];omega
  have hkhi : κ ≤ 6 := by dsimp [κ];omega
  by_cases h4 : κ=4
  · have hdiff : b.val-a.val=3 := by dsimp [κ] at h4;omega
    have hc : (a.val=1 ∧ b.val=4) ∨ (a.val=2 ∧ b.val=5) ∨ (a.val=3 ∧ b.val=6) := by omega
    rcases hc with h0|h1|h2
    · have ht := (strip_7_1_4 D k hq _ _ hab hu h0.1 h0.2).2.2
      omega
    · have ht := (strip_7_2_5 D k hq _ _ hab hu h1.1 h1.2).2.2
      omega
    · have ht := (strip_7_3_6 D k hq _ _ hab hu h2.1 h2.2).2.2
      omega
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 13 at hw
  have hc := coreP_count_add D k hq a b hab
  have hs := sigma_first_bounds D k hq a b hab
  change D.coreP k+(if κ ≤ D.u/2 then (D.u/2-κ+2).choose 2 else 0) ≤
    2*D.u-κ-1+(D.u/2).choose 2 at hc
  change D.internalSigma k hq ≤ min (D.u/2+1) κ at hs
  rw [hu] at hc hs
  have hf := D.actual_two_row_one k hq
  interval_cases hk : κ <;> norm_num [hk,Nat.choose] at hc hs <;> omega

theorem actual_first_8 (k : Type) [Field k] (hq : D.q=2) (hu : D.u=8) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ 29 := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  have ha := D.a_pos _ a.property
  have hb := D.a_lt _ b.property
  have hab' := hab.1
  have hg := pair_gcd D a b hab
  let κ := D.u-b.val+a.val
  have hklo : 2 ≤ κ := by dsimp [κ];omega
  have hkhi : κ ≤ 7 := by dsimp [κ];omega
  by_cases h4 : κ=4
  · have hdiff : b.val-a.val=4 := by dsimp [κ] at h4;omega
    have hc : (a.val=1 ∧ b.val=5) ∨ (a.val=2 ∧ b.val=6) ∨ (a.val=3 ∧ b.val=7) := by omega
    rcases hc with h0|h1|h2
    · have ht := (strip_8_1_5 D k hq _ _ hab hu h0.1 h0.2).2.2
      omega
    · norm_num [hu,h1.1,h1.2] at hg
    · have ht := (strip_8_3_7 D k hq _ _ hab hu h2.1 h2.2).2.2
      omega
  by_cases h5 : κ=5
  · have hdiff : b.val-a.val=3 := by dsimp [κ] at h5;omega
    have hc : (a.val=1 ∧ b.val=4) ∨ (a.val=2 ∧ b.val=5) ∨ (a.val=3 ∧ b.val=6) ∨ (a.val=4 ∧ b.val=7) := by omega
    rcases hc with h0|h1|h2|h3
    · have ht := (strip_8_1_4 D k hq _ _ hab hu h0.1 h0.2).2.2
      omega
    · have ht := (strip_8_2_5 D k hq _ _ hab hu h1.1 h1.2).2.2
      omega
    · have ht := (strip_8_3_6 D k hq _ _ hab hu h2.1 h2.2).2.2
      omega
    · have ht := (strip_8_4_7 D k hq _ _ hab hu h3.1 h3.2).2.2
      omega
  by_cases h6 : κ=6
  · have hdiff : b.val-a.val=2 := by dsimp [κ] at h6;omega
    have hc : (a.val=1 ∧ b.val=3) ∨ (a.val=2 ∧ b.val=4) ∨ (a.val=3 ∧ b.val=5) ∨ (a.val=4 ∧ b.val=6) ∨ (a.val=5 ∧ b.val=7) := by omega
    rcases hc with h0|h1|h2|h3|h4
    · have ht := (strip_8_1_3 D k hq _ _ hab hu h0.1 h0.2).2.2
      omega
    · norm_num [hu,h1.1,h1.2] at hg
    · have ht := (strip_8_3_5 D k hq _ _ hab hu h2.1 h2.2).2.2
      omega
    · norm_num [hu,h3.1,h3.2] at hg
    · have ht := (strip_8_5_7 D k hq _ _ hab hu h4.1 h4.2).2.2
      omega
  have hr := actualR_add_volume D k
  have hw := distance_volume_floor D hq
  rw [hu] at hr hw
  change D.wordVolume ≤ 17 at hw
  have hc := coreP_count_add D k hq a b hab
  have hs := sigma_first_bounds D k hq a b hab
  change D.coreP k+(if κ ≤ D.u/2 then (D.u/2-κ+2).choose 2 else 0) ≤
    2*D.u-κ-1+(D.u/2).choose 2 at hc
  change D.internalSigma k hq ≤ min (D.u/2+1) κ at hs
  rw [hu] at hc hs
  have hf := D.actual_two_row_one k hq
  interval_cases hk : κ <;> norm_num [hk,Nat.choose] at hc hs <;> omega



/-- In width six, a height-three point forces exactly the exceptional original orientation. -/
theorem height_six_nonexception (_hq : D.q=2) (a b : D.a) (hab : OrderedPair D a b)
    (hu : D.u=6) (hne : ¬(a.val=1 ∧ b.val=5)) : D.coreHeight ≤ 2 := by
  unfold Endpoint.Data.coreHeight
  apply Finset.sup_le
  intro r _
  apply Finset.sup_le
  intro c hc
  have hc' := (D.mem_minimalPoints r c).mp hc
  by_cases hr : r.val=0
  · have hr' : r=⟨0,D.u_pos⟩ := Fin.ext hr
    subst r
    rw [D.minimalFiber_zero c hc']
    exact Nat.zero_le _
  · let p : D.CoreMinimalIndex := ⟨⟨D.decodeCoordinate (r,c),hc'.prop⟩,by
      change Minimal (·∈D.coreFiber (D.coreCoordinates _).1) (D.coreCoordinates _).2
      rw [D.coreCoordinates_decode]
      exact hc'⟩
    obtain ⟨s,t,he⟩ := minimal_representation D a b hab p
    have hstd : Standard D a b (s,t) := by
      change D.CoreMinimal (word D a b s t)
      rw [←he]
      exact p.property
    have hneq : a≠b := fun h => (ne_of_lt hab.1) (congrArg (fun z : D.a => z.val) h)
    have hlen := standard_length_bound D a b hneq s t hstd
    have hd := congrArg D.coreDegree he
    rw [word_degree] at hd
    change c.1+c.2+D.epsilon r=s+t at hd
    have heps : D.epsilon r=1 := by simp only [Endpoint.Data.epsilon,ite_eq_right hr]
    rw [heps] at hd
    by_contra hL
    have hfour : s+t=4 := by omega
    have hK : c.2=0 := by omega
    have hoff := congrArg (fun z : D.corePoints => z.val.2) he
    change r.val+D.u*c.2=s*a.val+t*b.val at hoff
    rw [hK,mul_zero,add_zero] at hoff
    have hrange := r.isLt
    have ha := D.a_pos _ a.property
    have hb := D.a_lt _ b.property
    have hab' := hab.1
    by_cases hs : s=0
    · have ht : t=4 := by omega
      rw [hs,ht,zero_mul,zero_add] at hoff
      omega
    by_cases ht : t=0
    · have hs4 : s=4 := by omega
      rw [hs4,ht,zero_mul,add_zero] at hoff
      have ha1 : a.val=1 := by omega
      have hrel := standard_relations_bound D a b hab.1 s t hstd
      exact hne ⟨ha1,by omega⟩
    have hm := standard_mixed_bound D a b hneq s t (by omega) (by omega) hstd
    omega

theorem actual_first_six (k : Type) [Field k] (hq : D.q=2) (hu : D.u=6) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ 16 := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  by_cases he : a.val=1 ∧ b.val=5
  · exact (strip_6_1_5 D k hq a b hab hu he.1 he.2).2.2
  have hH := height_six_nonexception D hq a b hab hu he
  have hr := D.actualR_le_height k
  have hz : D.coreHeight-2=0 := by omega
  rw [hz,mul_zero] at hr
  have hp := D.coreP_le_wordVolume k
  have hw := distance_volume_floor D hq
  rw [hu] at hw
  change D.wordVolume ≤ 10 at hw
  have hs := sigma_first_bounds D k hq a b hab
  rw [hu] at hs
  have hs4 : D.internalSigma k hq ≤ 4 := hs.trans (min_le_left _ _)
  have hf := D.actual_two_row_one k hq
  omega


/-- The two-by-two downset has P+sigma≤5, including both possible corners. -/
theorem box_two_joint (k : Type) [Field k] (hq : D.q=2) (a b : D.a)
    (hab : OrderedPair D a b) (hS : ¬Standard D a b (2,0)) (hT : ¬Standard D a b (0,2)) :
    D.coreP k+D.internalSigma k hq ≤ 5 := by
  have hbox (p : ℕ×ℕ) (hp : Standard D a b p) : p.1<2 ∧ p.2<2 := by
    constructor
    · by_contra hn
      exact hS (standard_downward D a b p (2,0) hp ⟨by omega,Nat.zero_le _⟩)
    · by_contra hn
      exact hT (standard_downward D a b p (0,2) hp ⟨Nat.zero_le _,by omega⟩)
  have hp4 : D.coreP k ≤ 4 := by
    rw [coreP_card D k a b hab]
    have hi : standardWords D a b ⊆ (Finset.range 2).product (Finset.range 2) := by
      intro p hp
      have hb := hbox p ((mem_standardWords D a b p).mp hp)
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr hb.1,Finset.mem_range.mpr hb.2⟩
    exact (Finset.card_le_card hi).trans_eq (by decide)
  have hs2 : D.internalSigma k hq ≤ 2 := sigma_le_forbidden D k hq a b hab 2 0 hS
  by_cases hxy : Standard D a b (1,1)
  · have hs1 : D.internalSigma k hq ≤ 1 := by
      rw [sigma_card D k hq a b hab]
      have hi : socleWords D a b ⊆ {(1,1)} := by
        intro p hp
        have hs := (mem_socleWords D a b p).mp hp
        have hb := hbox p hs.1
        have h1 : p.1=1 := by
          by_contra hn
          have hz : p.1=0 := by omega
          exact hs.2.1 (standard_downward D a b (1,1) (p.1+1,p.2) hxy ⟨by omega,by omega⟩)
        have h2 : p.2=1 := by
          by_contra hn
          have hz : p.2=0 := by omega
          exact hs.2.2 (standard_downward D a b (1,1) (p.1,p.2+1) hxy ⟨by omega,by omega⟩)
        exact Finset.mem_singleton.mpr (Prod.ext h1 h2)
      simpa only [Finset.card_singleton] using Finset.card_le_card hi
    omega
  · have hp3 : D.coreP k ≤ 3 := by
      rw [coreP_card D k a b hab]
      have hi : standardWords D a b ⊆ ((Finset.range 2).product (Finset.range 2)).erase (1,1) := by
        intro p hp
        have hs := (mem_standardWords D a b p).mp hp
        have hb := hbox p hs
        apply Finset.mem_erase.mpr
        refine ⟨?_,Finset.mem_product.mpr ⟨Finset.mem_range.mpr hb.1,Finset.mem_range.mpr hb.2⟩⟩
        intro he
        exact hxy (he ▸ hs)
      exact (Finset.card_le_card hi).trans_eq (by decide)
    omega


theorem ordered_pair_finset (a b : D.a) (hab : OrderedPair D a b) : D.a={a.val,b.val} := by
  ext x
  constructor
  · intro hx
    rcases hab.2 ⟨x,hx⟩ with hx|hx
    · exact Finset.mem_insert.mpr (Or.inl (congrArg (fun z : D.a => z.val) hx))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (congrArg (fun z : D.a => z.val) hx)))
  · intro hx
    rcases Finset.mem_insert.mp hx with hx|hx
    · rw [hx];exact a.property
    · rw [Finset.mem_singleton.mp hx];exact b.property

theorem ordinary_four_first (k : Type) [Field k] (hq : D.q=2) (hu : D.u=4)
    (ha : D.a≠{1,3}) : totalBetti k D.Variables (D.fullG k) 1 ≤ 6 := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  have hap := D.a_pos _ a.property
  have hbl := D.a_lt _ b.property
  have hab' := hab.1
  have hne : ¬(a.val=1 ∧ b.val=3) := by
    intro h
    apply ha
    simpa only [h.1,h.2] using ordered_pair_finset D a b hab
  have hc : (a.val=1 ∧ b.val=2) ∨ (a.val=2 ∧ b.val=3) := by omega
  have hS : ¬Standard D a b (2,0) := by
    rcases hc with hc|hc
    · apply relation_forbidden D a b 2 0 0 1 1 0 <;> norm_num [hc.1,hc.2]
    · apply relation_forbidden D a b 2 0 0 0 1 1 <;> norm_num [hu,hc.1,hc.2]
  have hT : ¬Standard D a b (0,2) := by
    rcases hc with hc|hc
    · apply relation_forbidden D a b 0 2 0 0 1 1 <;> norm_num [hu,hc.1,hc.2]
    · apply relation_forbidden D a b 0 2 1 0 0 1 <;> norm_num [hu,hc.1,hc.2]
  have hj := box_two_joint D k hq a b hab hS hT
  have hr := actualR_zero_small D k hq a b hab (by omega)
  have hf := D.actual_two_row_one k hq
  omega

theorem actual_first_four_coarse (k : Type) [Field k] (hq : D.q=2) (hu : D.u=4) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ 8 := by
  obtain ⟨a,b,hab⟩ := ordered_pair_exists D hq
  have hp := D.coreP_le_wordVolume k
  have hw := distance_volume_floor D hq
  rw [hu] at hw
  change D.wordVolume ≤ 5 at hw
  have hσ : D.internalSigma k hq ≤ 2 := by
    have ht := socle_triangle_card D k hq a b hab
    by_contra hn
    have hl := Nat.choose_le_choose 2 (show 4 ≤ D.internalSigma k hq+1 by omega)
    change 6 ≤ (D.internalSigma k hq+1).choose 2 at hl
    omega
  have hr := actualR_zero_small D k hq a b hab (by omega)
  have hf := D.actual_two_row_one k hq
  omega


/-- All retained V06 small-width cases, on the original S and its literal target. -/
theorem narrow_four_small (S : NumericalSemigroup) (k : Type) [Field k]
    (he : S.embeddingDimension=4) (hw : S.width ≤ S.multiplicity-2) :
    let D := S.endpointData (by omega) hw
    (D.u=3 ∨ D.u=5 ∨ D.u=6 ∨ D.u=7 ∨ D.u=8 ∨
      (D.u=4 ∧ (D.d≠1 ∨ D.a≠{1,3}))) → ∀ i : ℕ,
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤
      totalBetti k (S.intervalCompletion (by omega)).AtomExponent
        (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
          ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  dsimp only
  intro hu i
  let D := S.endpointData (by omega) hw
  change D.u=3 ∨ D.u=5 ∨ D.u=6 ∨ D.u=7 ∨ D.u=8 ∨
      (D.u=4 ∧ (D.d≠1 ∨ D.a≠{1,3})) at hu
  have hq : D.q=2 := by
    have h := S.endpointData_embedding (by omega) hw
    change D.q+2=S.embeddingDimension at h
    omega
  by_cases h3 : D.u=3
  · exact S.narrow_four_fullAP_comparison k (by omega) hw (by change D.u=D.q+1;omega) i
  by_cases hi0 : i=0
  · subst i
    rw [S.completed_totalBetti_zero k,S.interval_completed_betti_zero k]
  by_cases hi2 : 2 ≤ i
  · exact narrow_four_higher S k he hw i hi2
  have hi1 : i=1 := by omega
  subst i
  rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k 1,
    ←D.fullG_totalBetti k]
  have ht := physical_capacity S k (by omega) hw 1 (by omega)
  change Target.apLowerProfile D.u 1 ≤ _ at ht
  rcases hu with hu|hu|hu|hu|hu|⟨hu,hd|ha⟩
  · contradiction
  · have hb := actual_first_five D k hq hu
    rw [hu] at ht
    exact hb.trans ((show 11 ≤ Target.apLowerProfile 5 1 by decide).trans ht)
  · have hb := actual_first_six D k hq hu
    rw [hu] at ht
    exact hb.trans ((show 16 ≤ Target.apLowerProfile 6 1 by decide).trans ht)
  · have hb := actual_first_7 D k hq hu
    rw [hu] at ht
    exact hb.trans ((show 22 ≤ Target.apLowerProfile 7 1 by decide).trans ht)
  · have hb := actual_first_8 D k hq hu
    rw [hu] at ht
    exact hb.trans ((show 29 ≤ Target.apLowerProfile 8 1 by decide).trans ht)
  · have hb := actual_first_four_coarse D k hq hu
    have hSw : S.width=D.d*D.u := by
      change S.width=S.offsetGcd*S.normalizedWidth
      rw [Nat.mul_comm,S.width_factor]
    have hd2 : 2 ≤ D.d := by have := D.d_pos;omega
    have hV : 8 ≤ S.width := by rw [hSw,hu];omega
    have htarget := S.interval_completed_betti_lower k (by omega) 1 (by omega)
    rw [min_eq_left (show S.width ≤ S.multiplicity-1 by omega)] at htarget
    have hpay := (Target.apLowerProfile_monotone 1 hV).trans htarget
    exact hb.trans ((show 8 ≤ Target.apLowerProfile 8 1 by decide).trans hpay)
  · have hb := ordinary_four_first D k hq hu ha
    rw [hu] at ht
    exact hb.trans ((show 6 ≤ Target.apLowerProfile 4 1 by decide).trans ht)
end NSP14.NarrowFour
