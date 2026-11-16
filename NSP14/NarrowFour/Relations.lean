module
public import NSP14.NarrowFour.StandardWords
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.NarrowFour
variable (D : Endpoint.Data)

/-- Integer degree and offset equality give a genuine endpoint factor in the original core. -/
theorem relation_forbidden (a b : D.a) (s t r w L K : ℕ)
    (hd : s+t=r+w+L+K)
    (ho : s*a.val+t*b.val=r*a.val+w*b.val+K*D.u) (hne : 0<L+K) :
    ¬Standard D a b (s,t) := by
  have hf : word D a b s t=word D a b r w+D.coreEndpointPoint (L,K) := by
    apply Subtype.ext
    change (word D a b s t).val=(word D a b r w).val+(D.coreEndpointPoint (L,K)).val
    rw [word_coe,word_coe,D.coreEndpointPoint_coe]
    apply Prod.ext <;> dsimp
    · omega
    · nlinarith only [ho]
  intro hs
  have hz := D.minimal_endpoint_factor _ _ (L,K) hs hf
  have hL := congrArg Prod.fst hz
  have hK := congrArg Prod.snd hz
  change L=0 at hL
  change K=0 at hK
  omega

/-- y^b=x^(b-a) z^a; no unit-offset hypothesis. -/
theorem first_pure_relation (a b : D.a) (hab : a.val<b.val) :
    ¬Standard D a b (b.val,0) := by
  apply relation_forbidden D a b b.val 0 0 a.val (b.val-a.val) 0
  · omega
  · simp only [zero_mul,add_zero,zero_add];ring
  · omega

/-- z^(u-a)=y^(u-b) v^(b-a), in the original endpoint orientation. -/
theorem second_pure_relation (a b : D.a) (hab : a.val<b.val) :
    ¬Standard D a b (0,D.u-a.val) := by
  have hb := D.a_lt _ b.property
  apply relation_forbidden D a b 0 (D.u-a.val) (D.u-b.val) 0 0 (b.val-a.val)
  · omega
  · simp only [zero_mul,zero_add,add_zero]
    have ha : a.val+(b.val-a.val)=b.val := by omega
    have hu : (D.u-b.val)+b.val=D.u := by omega
    have hua : (D.u-a.val)+a.val=D.u := by omega
    nlinarith only [ha,hu,hua]
  · omega

/-- y^(u-b)z^a=x^(u-b)v^a. -/
theorem mixed_rectangle_relation (a b : D.a) :
    ¬Standard D a b (D.u-b.val,a.val) := by
  have hb := D.a_lt _ b.property
  have ha := D.a_pos _ a.property
  apply relation_forbidden D a b (D.u-b.val) a.val 0 0 (D.u-b.val) a.val
  · omega
  · simp only [zero_mul,zero_add]
    have hu : (D.u-b.val)+b.val=D.u := by omega
    nlinarith only [hu]
  · omega

theorem standard_relations_bound (a b : D.a) (hab : a.val<b.val)
    (s t : ℕ) (hp : Standard D a b (s,t)) :
    s<b.val ∧ t<D.u-a.val ∧ ¬(D.u-b.val ≤ s ∧ a.val ≤ t) := by
  refine ⟨?_,?_,?_⟩
  · by_contra hn
    exact first_pure_relation D a b hab
      (standard_downward D a b (s,t) (b.val,0) hp ⟨by omega,Nat.zero_le _⟩)
  · by_contra hn
    exact second_pure_relation D a b hab
      (standard_downward D a b (s,t) (0,D.u-a.val) hp ⟨Nat.zero_le _,by omega⟩)
  · intro hr
    exact mixed_rectangle_relation D a b
      (standard_downward D a b (s,t) (D.u-b.val,a.val) hp hr)

theorem sigma_first_bounds (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) :
    D.internalSigma k hq ≤ min (D.u/2+1) (D.u-b.val+a.val) := by
  have hu : 3 ≤ D.u := by have h := D.q_add_one_le_u;omega
  have hne : a≠b := fun h => (ne_of_lt hab.1) (congrArg (fun x : D.a => x.val) h)
  apply le_min
  · by_contra hn
    have hh : 0<D.u/2 := by omega
    have hs := standard_of_degree_lt_sigma D k hq a b hab 1 (D.u/2) (by omega)
    have hm := standard_mixed_bound D a b hne 1 (D.u/2) (by omega) hh hs
    omega
  · by_contra hn
    have hs := standard_of_degree_lt_sigma D k hq a b hab (D.u-b.val) a.val (by omega)
    exact mixed_rectangle_relation D a b hs
end NSP14.NarrowFour
