module
public import NSP14.Additive.EndpointVolume
public import NSP14.Width.Progression
@[expose] public section
open scoped BigOperators
namespace NSP14.Width

/-- The actual finite tail used by the endpoint distance theorem. -/
def growthVolume (u a s : ℕ) : ℕ := u+∑ j∈Finset.range u,(u-a-s*j)

theorem growthVolume_ge (u a s : ℕ) : u≤growthVolume u a s := Nat.le_add_right _ _

/-- Exact Euclidean-remainder formula, with denominators cleared over the integers. -/
theorem growthVolume_remainder (u a s : ℕ) (ha : 0<a) (hs : 0<s) (hau : a≤u) :
    let k := (u-a)/s
    let b := (u-a)%s
    2*(growthVolume u a s-u)=s*k*(k+1)+2*b*(k+1) := by
  dsimp only
  unfold growthVolume
  rw [Nat.add_sub_cancel_left]
  apply progression_sum (u-a) s ((u-a)/s) ((u-a)%s) u hs
  · have hd := Nat.div_le_self (u-a) s
    omega
  · have := Nat.div_add_mod (u-a) s
    omega
  · exact Nat.mod_lt _ hs

/-- A division-free quadratic resource bound valid for both parities of the alphabet size. -/
theorem growthVolume_quadratic (u a s : ℕ) (ha : 0<a) (hs : 0<s)
    (hau : a≤u) (has : a≤2*s) : a*growthVolume u a s≤u^2 := by
  let k := (u-a)/s
  let b := (u-a)%s
  have hrem : u=a+s*k+b := by
    have := Nat.mod_add_div (u-a) s
    dsimp [k,b]
    omega
  have hid := growthVolume_remainder u a s ha hs hau
  change 2*(growthVolume u a s-u)=s*k*(k+1)+2*b*(k+1) at hid
  have hge := growthVolume_ge u a s
  have hzero : growthVolume u a s-u+u=growthVolume u a s := Nat.sub_add_cancel hge
  have he : 2*u^2=2*a*growthVolume u a s+
      s*(2*s-a)*k^2+a*s*k+2*(2*s-a)*k*b+2*b^2 := by
    have hsub : 2*s-a+a=2*s := Nat.sub_add_cancel has
    nlinarith only [hid,hrem,hzero,hsub]
  have hn : 0≤s*(2*s-a)*k^2+a*s*k+2*(2*s-a)*k*b+2*b^2 := Nat.zero_le _
  nlinarith only [he,hn]
end NSP14.Width

namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

/-- Kneser controls the actual shortest-word volume of this same endpoint datum. -/
theorem wordVolume_le_growthVolume :
    D.wordVolume≤NSP14.Width.growthVolume D.u (D.q+1) ((D.q+2)/2) :=
  D.wordVolume_growth_bound

/-- Universal quadratic resource. No physical-width or characteristic restriction is needed. -/
theorem wordVolume_quadratic_bound : (D.q+1)*D.wordVolume≤D.u^2 := by
  have hq := D.q_two
  have hs : 0<(D.q+2)/2 := by omega
  have h := NSP14.Width.growthVolume_quadratic D.u (D.q+1) ((D.q+2)/2)
    (by omega) hs D.q_add_one_le_u (by omega)
  exact (Nat.mul_le_mul_left (D.q+1) D.wordVolume_le_growthVolume).trans h
end NSP14.Endpoint.Data
