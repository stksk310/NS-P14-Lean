module
import NSP14.NarrowFour.StandardWords
import Mathlib.Algebra.Field.ZMod
open NSP14
example (D : Endpoint.Data) (a b : D.a) (hab : a≠b) (s t : ℕ)
    (hs : 0<s) (ht : 0<t) (hp : NarrowFour.Standard D a b (s,t)) :
    2*(s+t)≤D.u := NarrowFour.standard_mixed_bound D a b hab s t hs ht hp

namespace NSP14.Tests.Run19Words
open NSP14.Homological

def collective : Endpoint.Data where
  m := 8
  d := 1
  u := 6
  a := {2,3}
  q_two := by decide
  a_pos := by decide
  a_lt := by decide
  u_lt := by decide
  d_pos := by decide
  offsets_coprime := by decide
  coprime := by decide

def ca : collective.a := ⟨2,by decide⟩
def cb : collective.a := ⟨3,by decide⟩

theorem collective_pair : NarrowFour.OrderedPair collective ca cb := by
  refine ⟨by decide,?_⟩
  intro c
  have hc : c.val=2 ∨ c.val=3 := by
    simpa only [collective,Finset.mem_insert,Finset.mem_singleton] using c.property
  rcases hc with hc|hc
  · exact Or.inl (Subtype.ext hc)
  · exact Or.inr (Subtype.ext hc)

theorem neither_unit : ¬Nat.Coprime ca.val collective.u ∧ ¬Nat.Coprime cb.val collective.u := by
  decide

theorem collective_triangle (k : Type) [Field k] :
    (collective.internalSigma k rfl+1).choose 2≤collective.coreP k :=
  NarrowFour.socle_triangle_card collective k rfl ca cb collective_pair

example : (collective.internalSigma ℚ rfl+1).choose 2≤collective.coreP ℚ := collective_triangle ℚ
example : (collective.internalSigma (ZMod 2) rfl+1).choose 2≤collective.coreP (ZMod 2) := collective_triangle (ZMod 2)
example : (collective.internalSigma (ZMod 3) rfl+1).choose 2≤collective.coreP (ZMod 3) := collective_triangle (ZMod 3)

theorem mixed_both_orders (s t : ℕ) (hs : 0<s) (ht : 0<t)
    (hp : NarrowFour.Standard collective ca cb (s,t)) :
    2*(s+t)≤collective.u ∧ 2*(t+s)≤collective.u := by
  exact ⟨NarrowFour.standard_mixed_bound collective ca cb (by decide) s t hs ht hp,
    NarrowFour.standard_mixed_bound collective cb ca (by decide) t s ht hs
      ((NarrowFour.standard_swap collective ca cb s t).mpr hp)⟩

theorem small_height_and_socle (D : Endpoint.Data) (k : Type) [Field k]
    (hq : D.q=2) (hu : D.u≤5) : D.coreHeight≤D.u-3 ∧ D.actualR k=0 := by
  obtain ⟨a,b,hab⟩ := NarrowFour.ordered_pair_exists D hq
  exact ⟨NarrowFour.coreHeight_two_bound D hq a b hab,
    NarrowFour.actualR_zero_small D k hq a b hab hu⟩
end NSP14.Tests.Run19Words
