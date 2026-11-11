module
public import NSP14.Endpoint.MinimalBounds
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem minimalFiber_iff_predecessors (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    Minimal (·∈D.coreFiber r) c ↔
      (c.1=0 ∨ (c.1-1,c.2)∉D.coreFiber r) ∧ (c.2=0 ∨ (c.1,c.2-1)∉D.coreFiber r) := by
  constructor
  · intro h
    constructor
    · by_cases h0 : c.1=0
      · exact Or.inl h0
      · right
        intro hp
        have he := h.eq_of_le hp ⟨Nat.sub_le _ _,le_rfl⟩
        have hL := congrArg Prod.fst he
        omega
    · by_cases h0 : c.2=0
      · exact Or.inl h0
      · right
        intro hp
        have he := h.eq_of_le hp ⟨le_rfl,Nat.sub_le _ _⟩
        have hK := congrArg Prod.snd he
        omega
  · rintro ⟨hL,hK⟩
    refine ⟨hc,?_⟩
    intro b hb hbc
    have hbL := hbc.1
    have hbK := hbc.2
    have heL : c.1≤b.1 := by
      by_contra h
      have hp := D.coreFiber_upward r hb (show b≤(c.1-1,c.2) from ⟨by omega,hbK⟩)
      rcases hL with hL|hL <;> first | omega | exact hL hp
    have heK : c.2≤b.2 := by
      by_contra h
      have hp := D.coreFiber_upward r hb (show b≤(c.1,c.2-1) from ⟨hbL,by omega⟩)
      rcases hK with hK|hK <;> first | omega | exact hK hp
    exact ⟨heL,heK⟩

def CoreMinimal (p : D.corePoints) : Prop :=
  Minimal (·∈D.coreFiber (D.coreCoordinates p).1) (D.coreCoordinates p).2

theorem core_not_minimal_iff_factor (p : D.corePoints) : ¬D.CoreMinimal p ↔
    (∃ q : D.corePoints,p=q+D.coreGeneratorPoint D.xVariable) ∨
      (∃ q : D.corePoints,p=q+D.coreGeneratorPoint D.vVariable) := by
  constructor
  · intro hn
    let c := (D.coreCoordinates p).2
    let r := (D.coreCoordinates p).1
    have hc : c∈D.coreFiber r := D.coordinate_mem_fiber p
    have hp : ¬((c.1=0 ∨ (c.1-1,c.2)∉D.coreFiber r) ∧ (c.2=0 ∨ (c.1,c.2-1)∉D.coreFiber r)) := by
      intro h
      exact hn ((D.minimalFiber_iff_predecessors r c hc).mpr h)
    have hor : (0<c.1 ∧ (c.1-1,c.2)∈D.coreFiber r) ∨ (0<c.2 ∧ (c.1,c.2-1)∈D.coreFiber r) := by
      push Not at hp
      by_cases hL : c.1=0 ∨ (c.1-1,c.2)∉D.coreFiber r
      · right
        have hbad := hp hL
        exact ⟨by omega,hbad.2⟩
      · left
        push Not at hL
        exact ⟨by omega,hL.2⟩
    rcases hor with h|h
    · left
      let q : D.corePoints := ⟨D.decodeCoordinate (r,(c.1-1,c.2)),h.2⟩
      refine ⟨q,?_⟩
      apply Subtype.ext
      rw [←D.decode_coreCoordinates p]
      apply Prod.ext
      · change c.1+c.2+D.epsilon r=c.1-1+c.2+D.epsilon r+1
        omega
      · change r.val+D.u*c.2=r.val+D.u*c.2+0
        omega
    · right
      let q : D.corePoints := ⟨D.decodeCoordinate (r,(c.1,c.2-1)),h.2⟩
      refine ⟨q,?_⟩
      apply Subtype.ext
      rw [←D.decode_coreCoordinates p]
      apply Prod.ext
      · change c.1+c.2+D.epsilon r=c.1+(c.2-1)+D.epsilon r+1
        omega
      · change r.val+D.u*c.2=r.val+D.u*(c.2-1)+D.u
        nlinarith [Nat.sub_add_cancel (show 1≤c.2 by omega)]
  · intro h hmin
    rcases h with ⟨q,hq⟩|⟨q,hq⟩
    · have hfac : p=q+D.coreEndpointPoint (1,0) := by simpa [coreEndpointPoint] using hq
      have hh := D.minimal_endpoint_factor p q (1,0) hmin hfac
      have he := congrArg Prod.fst hh
      norm_num at he
    · have hfac : p=q+D.coreEndpointPoint (0,1) := by simpa [coreEndpointPoint] using hq
      have hh := D.minimal_endpoint_factor p q (0,1) hmin hfac
      have he := congrArg Prod.snd hh
      norm_num at he
end NSP14.Endpoint.Data
