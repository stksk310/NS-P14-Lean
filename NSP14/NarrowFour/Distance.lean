module
public import NSP14.NarrowFour.SocleTriangle
public import NSP14.Additive.QuadraticVolume
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.NarrowFour
variable (D : Endpoint.Data)

/-- The same actual shortest-path resource, retaining the parity floor. -/
theorem distance_volume_floor (hq : D.q=2) : D.wordVolume≤1+(D.u*D.u)/4 :=
  D.wordVolume_two_bound hq

theorem distance_volume_four (hq : D.q=2) : 4*(D.wordVolume-1)≤D.u^2 := by
  have h := distance_volume_floor D hq
  have hs : D.wordVolume-1≤(D.u*D.u)/4 := by omega
  calc
    4*(D.wordVolume-1)≤4*((D.u*D.u)/4) := Nat.mul_le_mul_left 4 hs
    _≤D.u^2 := by simpa only [pow_two,mul_comm] using Nat.div_mul_le_self (D.u*D.u) 4

theorem distance_volume_four_add (hq : D.q=2) : 4*D.wordVolume≤D.u^2+4 := by
  have h := distance_volume_floor D hq
  have hd := Nat.div_mul_le_self (D.u*D.u) 4
  nlinarith only [h,hd]

theorem sigma_le_width (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) : D.internalSigma k hq≤D.u-1 := by
  have htri := socle_triangle_card D k hq a b hab
  have hP := D.coreP_le_wordVolume k
  have hW := distance_volume_four_add D hq
  have hu : 3≤D.u := by have h := D.q_add_one_le_u; omega
  by_contra hn
  have hs : D.u≤D.internalSigma k hq := by omega
  have hm := Nat.mul_le_mul hs (Nat.succ_le_succ hs)
  have hc := Nat.add_one_mul_choose_eq (D.internalSigma k hq) 1
  simp only [Nat.choose_one_right] at hc
  nlinarith only [htri,hP,hW,hu,hm,hc]

end NSP14.NarrowFour
