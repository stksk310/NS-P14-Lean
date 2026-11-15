module
public import NSP14.SmallEmbedding.ThreePresentation
public import NSP14.Homological.FiniteKoszulEulerAbove
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical BigOperators
open CategoryTheory NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : ThreeData)

/-- The actual one-letter alphabet, without a unit-label or characteristic assumption. -/
theorem one_letter_exists (hq : D.q=1) : ∃ a : D.a,∀ b : D.a,b=a := by
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hq
  refine ⟨⟨a,by rw [ha];exact Finset.mem_singleton_self _⟩,?_⟩
  intro b
  apply Subtype.ext
  let x : ℕ := b.val
  have hx : x∈D.a := b.property
  rw [ha,Finset.mem_singleton] at hx
  exact hx

/-- Every actual core-minimal point is one pure word. -/
theorem one_minimal_pure (a : D.a) (ha : ∀ b : D.a,b=a) (p : D.CoreMinimalIndex) :
    p.val=D.coreDegree p.val • D.coreGeneratorPoint (D.internalVariable a) := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hm : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2 := by rw [hw];exact p.property
  have hall : ∀ b∈w,b=D.internalVariable a := by
    intro b hb
    have hin := D.minimal_word_internal w hm b hb
    have he := ha ⟨b.val,hin⟩
    exact Subtype.ext (congrArg (fun z : D.a => z.val) he)
  have hwords : ∀ v : List D.Variables,(∀ b∈v,b=D.internalVariable a) →
      D.coreWord v=v.length • D.coreGeneratorPoint (D.internalVariable a) := by
    intro v
    induction v with
    | nil => intro _;simp only [coreWord_nil,List.length_nil,zero_nsmul]
    | cons b v ih =>
      intro hv
      rw [D.coreWord_cons,hv b (by simp),ih (by intro c hc;exact hv c (by simp [hc])),List.length_cons]
      rw [add_nsmul,one_nsmul]
      abel
  rw [←hw,D.coreWord_degree]
  exact hwords w hall

def minimalDegreeIndex (p : D.CoreMinimalIndex) : Fin D.u := ⟨D.coreDegree p.val,D.coreMinimal_degree_lt p⟩

theorem minimalDegreeIndex_injective (hq : D.q=1) : Function.Injective D.minimalDegreeIndex := by
  obtain ⟨a,ha⟩ := D.one_letter_exists hq
  intro p q he
  have hd := congrArg Fin.val he
  apply Subtype.ext
  rw [D.one_minimal_pure a ha p,D.one_minimal_pure a ha q]
  change D.coreDegree p.val=D.coreDegree q.val at hd
  rw [hd]

theorem one_coreP_bound (k : Type) [Field k] (hq : D.q=1) : D.coreP k ≤ D.u := by
  have h := Fintype.card_le_of_injective D.minimalDegreeIndex (D.minimalDegreeIndex_injective hq)
  have hP : D.coreP k=Fintype.card D.CoreMinimalIndex := Module.finrank_eq_card_basis (D.QCoreBasis k)
  rw [hP]
  simpa only [Fintype.card_fin] using h

variable (k : Type) [Field k]

theorem QCore_one_betti_one (hq : D.q=1) : totalBetti k D.a (D.QCoreModule k) 1=1 := by
  have h := finite_koszul_bettiEuler_top k D.a (D.QCoreModule k)
    (by rw [Fintype.card_coe];change 1 ≤ D.q;omega)
  rw [Fintype.card_coe,show D.a.card=1 from hq,bettiEuler_succ,bettiEuler_zero,D.QCore_betti_zero] at h
  change (totalBetti k D.a (D.QCoreModule k) 1:ℤ)-1=0 at h
  omega

theorem QCore_one_betti_above (hq : D.q=1) (i : ℕ) (hi : 1 < i) :
    totalBetti k D.a (D.QCoreModule k) i=0 :=
  totalBetti_eq_zero_of_gt k D.a _ i (by rw [Fintype.card_coe];change D.q < i;omega)

/-- All three actual rows retain the same original P_C and endpoint socle R. -/
theorem actual_one_rows (hq : D.q=1) :
    totalBetti k D.Variables (D.fullG k) 1 ≤ D.coreP k+D.actualR k+1 ∧
    totalBetti k D.Variables (D.fullG k) 2 ≤ D.coreP k+2*D.actualR k ∧
    totalBetti k D.Variables (D.fullG k) 3 ≤ D.actualR k := by
  have h1 := D.actual_core_endpoint_bound k 1
  have h2 := D.actual_core_endpoint_bound k 2
  have h3 := D.actual_endpoint_top k
  rw [D.QCore_one_betti_one k hq] at h1
  rw [D.QCore_one_betti_above k hq 2 (by omega)] at h2
  norm_num [coreRemainder,hq,Nat.choose] at h1 h2 h3
  exact ⟨by omega,by omega,h3⟩


/-- Each real minimal core point pays for its own positive competitors. -/
def coreCost (p : D.CoreMinimalIndex) : ℕ := (D.coreCoordinates p.val).2.1-2
abbrev BudgetIndex := Σ p : D.CoreMinimalIndex,Fin (D.coreCost p)
abbrev CompetitorMinimalIndex := Σ s : Fin D.u,{c : ℕ×ℕ // Minimal (·∈D.competitorFiber s) c}

noncomputable instance competitorMinimalFintype (s : Fin D.u) :
    Fintype {c : ℕ×ℕ // Minimal (·∈D.competitorFiber s) c} :=
  @Fintype.ofFinite _ (D.competitorMin_finite s).to_subtype

def budgetImage (z : D.BudgetIndex) : D.Coordinate :=
  (D.shiftedResidue (D.coreCoordinates z.1.val).1 (z.2.val+1),
    D.forbiddenStart (D.coreCoordinates z.1.val).1 (z.2.val+1) (D.coreCoordinates z.1.val).2)

theorem positive_minimal_witness (x : D.CompetitorMinimalIndex) (hx : 0<x.2.val.1) :
    ∃ z : D.BudgetIndex,D.budgetImage z=(x.1,x.2.val) := by
  obtain ⟨r,j,hj,a,ha,hs,hstart⟩ := x.2.property.prop
  obtain ⟨b,hba,hb⟩ := D.exists_minimalFiber_le r a ha
  have hstart' : D.forbiddenStart r j b ≤ x.2.val := by
    apply (D.forbiddenStart_le r j b x.2.val).mpr
    have h := (D.forbiddenStart_le r j a x.2.val).mp hstart
    obtain ⟨hL,hK⟩ := hba
    constructor <;> omega
  have hmem : D.forbiddenStart r j b∈D.competitorFiber x.1 := ⟨r,j,hj,b,hb.prop,hs,le_rfl⟩
  have he := x.2.property.eq_of_le hmem hstart'
  have hheight := D.forbiddenStart_height r j b.1 b.2 b.1 le_rfl
  change (D.forbiddenStart r j b).1 ≤ b.1-2*j at hheight
  rw [he] at hheight
  let p : D.CoreMinimalIndex := ⟨⟨D.decodeCoordinate (r,b),hb.prop⟩,by
    change Minimal (·∈D.coreFiber (D.coreCoordinates _).1) (D.coreCoordinates _).2
    rw [D.coreCoordinates_decode]
    exact hb⟩
  have hp : D.coreCoordinates p.val=(r,b) := D.coreCoordinates_decode r b hb.prop
  have hbound : j-1<D.coreCost p := by
    unfold coreCost
    rw [hp]
    dsimp
    omega
  refine ⟨⟨p,⟨j-1,hbound⟩⟩,?_⟩
  change (D.shiftedResidue (D.coreCoordinates p.val).1 (j-1+1),
    D.forbiddenStart (D.coreCoordinates p.val).1 (j-1+1) (D.coreCoordinates p.val).2)=(x.1,x.2.val)
  rw [hp,Nat.sub_add_cancel hj]
  exact Prod.ext hs he

noncomputable def minimalEncoding (x : D.CompetitorMinimalIndex) : Fin D.u ⊕ D.BudgetIndex :=
  if hx : x.2.val.1=0 then Sum.inl x.1 else
    Sum.inr (D.positive_minimal_witness x (by omega)).choose

theorem minimalEncoding_injective : Function.Injective D.minimalEncoding := by
  rintro ⟨s,c⟩ ⟨t,d⟩ he
  by_cases hx : c.val.1=0
  · by_cases hy : d.val.1=0
    · unfold minimalEncoding at he
      rw [dite_eq_left hx,dite_eq_left hy] at he
      have hst := Sum.inl.inj he
      change s=t at hst
      subst t
      have hcd : c=d := Subtype.ext (NSP14.Endpoint.minimal_pair_eq_of_fst c.property d.property (by omega))
      subst d
      rfl
    · unfold minimalEncoding at he
      rw [dite_eq_left hx,dite_eq_right hy] at he
      nomatch he
  · by_cases hy : d.val.1=0
    · unfold minimalEncoding at he
      rw [dite_eq_right hx,dite_eq_left hy] at he
      nomatch he
    · unfold minimalEncoding at he
      rw [dite_eq_right hx,dite_eq_right hy] at he
      have hw := Sum.inr.inj he
      have hwx := (D.positive_minimal_witness ⟨s,c⟩ (show 0<c.val.1 by omega)).choose_spec
      have hwy := (D.positive_minimal_witness ⟨t,d⟩ (show 0<d.val.1 by omega)).choose_spec
      rw [hw] at hwx
      have hxy : (s,c.val)=(t,d.val) := hwx.symm.trans hwy
      have hst := congrArg Prod.fst hxy
      change s=t at hst
      subst t
      have hcd : c=d := Subtype.ext (congrArg Prod.snd hxy)
      subst d
      rfl

theorem competitor_sum_refined : (∑ s : Fin D.u,D.competitorZ s) ≤ ∑ p : D.CoreMinimalIndex,D.coreCost p := by
  have hc := Fintype.card_le_of_injective D.minimalEncoding D.minimalEncoding_injective
  simp only [Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] at hc
  have hmin (s : Fin D.u) : Fintype.card {c : ℕ×ℕ // Minimal (·∈D.competitorFiber s) c}=D.competitorZ s+1 := by
    rw [←Nat.card_eq_fintype_card]
    exact D.competitorMin_card s
  simp_rw [hmin] at hc
  rw [Finset.sum_add_distrib] at hc
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at hc
  omega

theorem actualR_refined : D.actualR k ≤ ∑ p : D.CoreMinimalIndex,D.coreCost p :=
  (D.actualR_le_sum_z k).trans D.competitor_sum_refined


theorem coreCost_degree (p : D.CoreMinimalIndex) : D.coreCost p ≤ D.coreDegree p.val-3 := by
  let r := (D.coreCoordinates p.val).1
  let c := (D.coreCoordinates p.val).2
  have hm : Minimal (·∈D.coreFiber r) c := p.property
  change c.1-2 ≤ D.coreDegree p.val-3
  by_cases hr : r.val=0
  · have hr' : r=⟨0,D.u_pos⟩ := Fin.ext hr
    rw [hr'] at hm
    have hc : c=0 := D.minimalFiber_zero c hm
    rw [hc]
    exact Nat.zero_le _
  · have hd := congrArg Prod.fst (D.decode_coreCoordinates p.val)
    change c.1+c.2+D.epsilon r=D.coreDegree p.val at hd
    have he : D.epsilon r=1 := by simp only [epsilon,ite_eq_right hr]
    rw [he] at hd
    omega

theorem sum_truncated_degree (u : ℕ) : (∑ n∈Finset.range u,(n-3))=(u-3).choose 2 := by
  induction u with
  | zero => decide
  | succ u ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases hu : 3 ≤ u
    · have hs : u+1-3=(u-3)+1 := by omega
      rw [hs,Nat.choose_succ_succ]
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Nat.choose_one_right]
      omega
    · interval_cases u <;> decide

/-- Aggregate original-orientation resource; the proof counts positive minimal
competitors by their actual long-side minimal word and positive jump. -/
theorem actualR_one_bound (hq : D.q=1) : D.actualR k ≤ (D.u-3).choose 2 := by
  calc
    D.actualR k ≤ ∑ p : D.CoreMinimalIndex,D.coreCost p := D.actualR_refined k
    _ ≤ ∑ p : D.CoreMinimalIndex,(D.coreDegree p.val-3) :=
      Finset.sum_le_sum (fun p _ => D.coreCost_degree p)
    _ ≤ ∑ n : Fin D.u,(n.val-3) := by
      apply Finset.sum_le_sum_of_injOn (s := Finset.univ) (t := Finset.univ) D.minimalDegreeIndex
        (fun _ _ _ _ h => D.minimalDegreeIndex_injective hq h) (Finset.subset_univ _)
      · intro p _
        exact le_rfl
      · intros
        exact Nat.zero_le _
    _=(D.u-3).choose 2 := by
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => n-3) D.u,sum_truncated_degree]
end NSP14.SmallEmbedding.ThreeData
