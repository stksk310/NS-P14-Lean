module
public import NSP14.Endpoint.MinimalWords
public import NSP14.Endpoint.OffsetOrder
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem coreCoordinates_decode (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    D.coreCoordinates ⟨D.decodeCoordinate (r,c),hc⟩=(r,c) := by
  apply D.decodeCoordinate_injective
  exact D.decode_coreCoordinates _

theorem minimalFiber_degree_lt (r : Fin D.u) (c : ℕ×ℕ)
    (h : Minimal (·∈D.coreFiber r) c) : c.1+c.2+D.epsilon r<D.u := by
  let p : D.corePoints := ⟨D.decodeCoordinate (r,c),h.prop⟩
  obtain ⟨w,hw⟩ := D.exists_coreWord p
  have hc := D.coreCoordinates_decode r c h.prop
  change D.coreCoordinates p=(r,c) at hc
  have hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2 := by rw [hw,hc];exact h
  have hb := D.minimal_word_length_lt w hmin
  have hd := D.coreWord_degree w
  rw [hw] at hd
  change c.1+c.2+D.epsilon r=w.length at hd
  omega

theorem minimalFiber_zero (c : ℕ×ℕ) (h : Minimal (·∈D.coreFiber ⟨0,D.u_pos⟩) c) : c=0 := by
  exact (h.eq_of_le (D.coreFiber_zero (0,0)) bot_le).symm

/-- The exceptional residue zero is the unit ideal; all other minimal
points have epsilon one, so every minimal L+K is at most u-2. -/
theorem minimalFiber_budget (r : Fin D.u) (c : ℕ×ℕ)
    (h : Minimal (·∈D.coreFiber r) c) : c.1+c.2≤D.u-2 := by
  by_cases hr : r.val=0
  · have he : r=⟨0,D.u_pos⟩ := Fin.ext hr
    subst r
    rw [D.minimalFiber_zero c h]
    simp only [Prod.fst_zero,Prod.snd_zero,add_zero,Nat.zero_le]
  · have hb := D.minimalFiber_degree_lt r c h
    have he : D.epsilon r=1 := by simp only [epsilon,hr,ite_false]
    rw [he] at hb
    omega

theorem minimalFiber_finite (r : Fin D.u) : Set.Finite {c | Minimal (·∈D.coreFiber r) c} := by
  apply (Set.finite_Iic (D.u-2,D.u-2)).subset
  intro c hc
  have hb := D.minimalFiber_budget r c hc
  exact ⟨by omega,by omega⟩

/-- Minimal words use only the actual internal offsets. Endpoint
letters are excluded by deleting their singleton zero-residue segment. -/
theorem minimal_word_internal (w : List D.Variables)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2) : ∀ b∈w,b.val∈D.a := by
  intro b hb
  rcases (D.mem_offsets b.val).mp b.property with h0|hu|ha
  · obtain ⟨l,z,hw⟩ := List.mem_iff_append.mp hb
    have hmin' : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord (l++([b]++z)))).1)
        (D.coreCoordinates (D.coreWord (l++([b]++z)))).2 := by simpa only [List.singleton_append,←hw] using hmin
    have hh := D.minimal_word_zero_segment l [b] z hmin' (by
      change D.u∣b.val
      rw [h0]
      exact dvd_zero _)
    simp only [List.length_singleton] at hh
    omega
  · obtain ⟨l,z,hw⟩ := List.mem_iff_append.mp hb
    have hmin' : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord (l++([b]++z)))).1)
        (D.coreCoordinates (D.coreWord (l++([b]++z)))).2 := by simpa only [List.singleton_append,←hw] using hmin
    have hh := D.minimal_word_zero_segment l [b] z hmin' (by
      change D.u∣b.val
      rw [hu])
    simp only [List.length_singleton] at hh
    omega
  · exact ha

/-- A finite, pure internal, bounded-length representation is derived
for every actual minimal fiber point. -/
theorem exists_minimal_internal_word (r : Fin D.u) (c : ℕ×ℕ)
    (h : Minimal (·∈D.coreFiber r) c) :
    ∃ w : List D.Variables,D.coreCoordinates (D.coreWord w)=(r,c) ∧
      w.length≤D.u-1 ∧ ∀ b∈w,b.val∈D.a := by
  let p : D.corePoints := ⟨D.decodeCoordinate (r,c),h.prop⟩
  obtain ⟨w,hw⟩ := D.exists_coreWord p
  have hc := D.coreCoordinates_decode r c h.prop
  change D.coreCoordinates p=(r,c) at hc
  have hm : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2 := by rw [hw,hc];exact h
  exact ⟨w,by rw [hw,hc],by have := D.minimal_word_length_lt w hm;omega,D.minimal_word_internal w hm⟩
end NSP14.Endpoint.Data
