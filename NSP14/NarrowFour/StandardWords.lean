module
public import NSP14.NarrowFour.Distance
public import NSP14.Additive.StandardWordSequence
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.NarrowFour
variable (D : Endpoint.Data)

theorem word_swap (a b : D.a) (s t : ℕ) : word D b a t s=word D a b s t := by
  unfold word
  abel

theorem standard_swap (a b : D.a) (s t : ℕ) :
    Standard D b a (t,s) ↔ Standard D a b (s,t) := by
  change D.CoreMinimal (word D b a t s) ↔ D.CoreMinimal (word D a b s t)
  rw [word_swap]

theorem word_sequence (a b : D.a) (s t : ℕ) :
    D.indexedInternalWord (Fin.addCases (fun _ : Fin s => a) (fun _ : Fin t => b))=
      word D a b s t := by
  unfold Endpoint.Data.indexedInternalWord
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left,Fin.addCases_right,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,word]

theorem standard_zeroSumFree (a b : D.a) (s t : ℕ) (hp : Standard D a b (s,t)) :
    Additive.ZeroSumFree (Additive.twoValueSequence s t (a.val : ZMod D.u) (b.val : ZMod D.u)) := by
  let w : Fin (s+t) → D.a := Fin.addCases (fun _ : Fin s => a) (fun _ : Fin t => b)
  have hmin : D.CoreMinimal (D.indexedInternalWord w) := by
    rw [show D.indexedInternalWord w=word D a b s t from word_sequence D a b s t]
    exact hp
  have h := D.minimal_internal_word_zeroSumFree w hmin
  have he : D.internalWordSequence w=Additive.twoValueSequence s t
      (a.val : ZMod D.u) (b.val : ZMod D.u) := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
      simp only [Endpoint.Data.internalWordSequence,w,Additive.twoValueSequence,
        Fin.addCases_left,Fin.addCases_right]
  rwa [he] at h

/-- Return a unit-normalized group relation to the original integer offsets. -/
theorem power_relation_forbidden (a b : D.a) (c : ℕ) (hc : 2≤c)
    (he : (c : ZMod D.u)*(a.val : ZMod D.u)=(b.val : ZMod D.u)) :
    ¬Standard D a b (c,0) := by
  let K := c*a.val/D.u
  have hmod : (c*a.val)%D.u=b.val := by
    have hh := congrArg ZMod.val he
    rw [←Nat.cast_mul,ZMod.val_natCast,ZMod.val_natCast_of_lt (D.a_lt _ b.property)] at hh
    exact hh
  have hEq : c*a.val=b.val+K*D.u := by
    have hh := Nat.mod_add_div (c*a.val) D.u
    rw [hmod] at hh
    dsimp [K]
    nlinarith only [hh]
  have hm := Nat.mul_lt_mul_of_pos_left (D.a_lt _ a.property) (by omega : 0<c)
  have hKu : K*D.u<c*D.u := by omega
  have hK : K≤c-1 := by
    have hh := (Nat.mul_lt_mul_right D.u_pos).mp hKu
    omega
  have hfac : word D a b c 0=D.coreGeneratorPoint (D.internalVariable b)+
      D.coreEndpointPoint (c-1-K,K) := by
    apply Subtype.ext
    change (word D a b c 0).val=(1,b.val)+(D.coreEndpointPoint (c-1-K,K)).val
    rw [word_coe,D.coreEndpointPoint_coe]
    apply Prod.ext <;> dsimp
    · omega
    · nlinarith only [hEq]
  intro hmin
  have hz := D.minimal_endpoint_factor _ _ (c-1-K,K) hmin hfac
  have hL := congrArg Prod.fst hz
  have hR := congrArg Prod.snd hz
  change c-1-K=0 at hL
  change K=0 at hR
  omega

theorem standard_power_relation_bound (a b : D.a) (c s : ℕ) (hc : 2≤c)
    (he : (c : ZMod D.u)*(a.val : ZMod D.u)=(b.val : ZMod D.u))
    (hp : Standard D a b (s,0)) : s<c := by
  by_contra hn
  exact power_relation_forbidden D a b c hc he
    (standard_downward D a b (s,0) (c,0) hp ⟨by omega,le_rfl⟩)

theorem twoValue_budget (u R T c : ℕ) (hu : 0<u) (hc : 2≤c)
    (hR : R<c) (hT : 1≤T) (hS : R+c*T≤u-1) : 2*(R+T)≤u := by
  have hm := Nat.mul_le_mul_left (c-2) hT
  have hc' : c-2+2=c := Nat.sub_add_cancel hc
  have hsum : R+c*T+1≤u := by omega
  simp only [mul_one] at hm
  nlinarith only [hm,hc',hR,hsum]

/-- SC is used only on the word's residue sequence. Both possible label
orders return to a relation between the original actual core generators. -/
theorem standard_mixed_bound (a b : D.a) (hab : a≠b) (s t : ℕ)
    (hs : 0<s) (ht : 0<t) (hp : Standard D a b (s,t)) : 2*(s+t)≤D.u := by
  by_contra hn
  have hu : 2≤D.u := by have := D.a_pos _ a.property; have := D.a_lt _ a.property; omega
  have hv : (a.val : ZMod D.u)≠(b.val : ZMod D.u) := by
    intro he
    apply hab
    apply Subtype.ext
    have hh := congrArg ZMod.val he
    rwa [ZMod.val_natCast_of_lt (D.a_lt _ a.property),
      ZMod.val_natCast_of_lt (D.a_lt _ b.property)] at hh
  obtain ⟨_,c,hc,hcases⟩ := Additive.savchevChen_twoValue hu hs ht
    (a.val : ZMod D.u) (b.val : ZMod D.u) hv (standard_zeroSumFree D a b s t hp) (by omega)
  rcases hcases with ⟨_,_,hS,hrel⟩|⟨_,_,hS,hrel⟩
  · have hlt := standard_power_relation_bound D a b c s hc hrel
      (standard_downward D a b (s,t) (s,0) hp ⟨le_rfl,Nat.zero_le _⟩)
    exact hn (twoValue_budget D.u s t c D.u_pos hc hlt ht hS)
  · have hswap := (standard_swap D a b s t).mpr hp
    have hlt := standard_power_relation_bound D b a c t hc hrel
      (standard_downward D b a (t,s) (t,0) hswap ⟨le_rfl,Nat.zero_le _⟩)
    have hbound := twoValue_budget D.u t s c D.u_pos hc hlt hs hS
    omega

/-- A pure word of length u-1 forces SC to normalize its label to 1.
The second genuine label then supplies a forbidden power of degree at most u-1. -/
theorem standard_pure_bound (a b : D.a) (hab : a≠b) (s : ℕ)
    (hp : Standard D a b (s,0)) : s≤D.u-2 := by
  have hu : 3≤D.u := by have h := D.q_add_one_le_u; have hq : 2≤D.q := D.q_two; omega
  let : NeZero D.u := ⟨ne_of_gt D.u_pos⟩
  by_contra hn
  let n := D.u-1
  have hn0 : 0<n := by dsimp [n]; omega
  have hnle : n≤s := by dsimp [n]; omega
  have hstd := standard_downward D a b (s,0) (n,0) hp ⟨hnle,le_rfl⟩
  obtain ⟨c,hpos,hS⟩ := Additive.savchevChen_positive (by omega : 2≤D.u)
    (Additive.twoValueSequence n 0 (a.val : ZMod D.u) (b.val : ZMod D.u))
    (standard_zeroSumFree D a b n 0 hstd) (by dsimp [n]; omega)
  have hpa := (hpos (Fin.castAdd 0 ⟨0,hn0⟩)).1
  simp only [Additive.twoValueSequence,Fin.addCases_left] at hpa
  rw [Additive.twoValue_representativeSum] at hS
  simp only [zero_mul,add_zero] at hS
  have ha : ((c : ZMod D.u)*(a.val : ZMod D.u)).val=1 := by
    by_contra hne
    have h2 : 2≤((c : ZMod D.u)*(a.val : ZMod D.u)).val := by omega
    have hm := Nat.mul_le_mul_left n h2
    dsimp [n] at hm hS
    omega
  let r := ((c : ZMod D.u)*(b.val : ZMod D.u)).val
  have hr := Additive.normalized_modular_relation c (a.val : ZMod D.u) (b.val : ZMod D.u) ha rfl
  have hr0 : r≠0 := by
    intro hz
    change (r : ZMod D.u)*(a.val : ZMod D.u)=(b.val : ZMod D.u) at hr
    rw [hz,Nat.cast_zero,zero_mul] at hr
    have hv := congrArg ZMod.val hr
    rw [ZMod.val_zero,ZMod.val_natCast_of_lt (D.a_lt _ b.property)] at hv
    have hb := D.a_pos _ b.property
    omega
  have hr1 : r≠1 := by
    intro hz
    change (r : ZMod D.u)*(a.val : ZMod D.u)=(b.val : ZMod D.u) at hr
    rw [hz,Nat.cast_one,one_mul] at hr
    apply hab
    apply Subtype.ext
    have hv := congrArg ZMod.val hr
    rwa [ZMod.val_natCast_of_lt (D.a_lt _ a.property),
      ZMod.val_natCast_of_lt (D.a_lt _ b.property)] at hv
  have hr2 : 2≤r := by omega
  have hru : r<D.u := ZMod.val_lt _
  have hs := standard_power_relation_bound D a b r s hr2 hr hp
  dsimp [n] at hnle
  omega



/-- Every genuine two-variable standard word, including pure axes. -/
theorem standard_length_bound (a b : D.a) (hab : a≠b) (s t : ℕ)
    (hp : Standard D a b (s,t)) : s+t≤D.u-2 := by
  by_cases hs : s=0
  · subst s
    simpa only [zero_add] using standard_pure_bound D b a hab.symm t
      ((standard_swap D a b 0 t).mpr hp)
  by_cases ht : t=0
  · subst t
    simpa only [add_zero] using standard_pure_bound D a b hab s hp
  have hm := standard_mixed_bound D a b hab s t (by omega) (by omega) hp
  omega

/-- Original-coordinate height, with no reflection or unit change of source. -/
theorem coreHeight_two_bound (_hq : D.q=2) (a b : D.a) (hab : OrderedPair D a b) :
    D.coreHeight≤D.u-3 := by
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
    have hne : a≠b := fun h => (ne_of_lt hab.1) (congrArg (fun x : D.a => x.val) h)
    have hstd : Standard D a b (s,t) := by
      change D.CoreMinimal (word D a b s t)
      rw [←he]
      exact p.property
    have hlen := standard_length_bound D a b hne s t hstd
    have hd := congrArg D.coreDegree he
    rw [word_degree] at hd
    change c.1+c.2+D.epsilon r=s+t at hd
    have heps : D.epsilon r=1 := by simp only [Endpoint.Data.epsilon,ite_eq_right hr]
    rw [heps] at hd
    omega

theorem actualR_zero_small (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) (hu : D.u≤5) : D.actualR k=0 := by
  have hH := coreHeight_two_bound D hq a b hab
  have hR := D.actualR_le_height k
  have hz : D.coreHeight-2=0 := by omega
  rw [hz,mul_zero] at hR
  omega

end NSP14.NarrowFour
