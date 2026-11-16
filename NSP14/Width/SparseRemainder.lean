module
public import NSP14.Width.SparseVolume
public import Mathlib.Tactic.IntervalCases
@[expose] public section
namespace NSP14.Width

theorem growthVolume_remainder_identity (u a s : ℕ) (ha : 0<a) (hs : 0<s) (hau : a≤u) :
    2*s*growthVolume u a s=2*s*u+(u-a)^2+s*(u-a)+
      ((u-a)%s)*(s-(u-a)%s) := by
  let k := (u-a)/s
  let b := (u-a)%s
  have hu : u=a+s*k+b := by
    have := Nat.mod_add_div (u-a) s
    dsimp [k,b]
    omega
  exact progression_volume_identity a s k b u (growthVolume u a s) hu (Nat.mod_lt _ hs)
    (growthVolume_remainder u a s ha hs hau) (growthVolume_ge u a s)
end NSP14.Width
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem wordVolume_remainder_upper :
    let a := D.q+1
    let s := (D.q+2)/2
    2*s*D.wordVolume≤2*s*D.u+(D.u-a)^2+s*(D.u-a)+
      ((D.u-a)%s)*(s-(D.u-a)%s) := by
  dsimp only
  have hq := D.q_two
  have he := NSP14.Width.growthVolume_remainder_identity D.u (D.q+1) ((D.q+2)/2)
    (by omega) (by omega) D.q_add_one_le_u
  rw [←he]
  exact Nat.mul_le_mul_left _ D.wordVolume_le_growthVolume

theorem wordVolume_q_four (hq : D.q=4) : 6*D.wordVolume+D.u≤D.u^2+12 := by
  have h := D.wordVolume_remainder_upper
  dsimp only at h
  rw [hq] at h
  norm_num only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceMul] at h
  have hb : (D.u-5)%3<3 := Nat.mod_lt _ (by decide)
  have hr : ((D.u-5)%3)*(3-(D.u-5)%3)≤2 := by
    interval_cases b : (D.u-5)%3 <;> norm_num
  have hu := D.q_add_one_le_u
  rw [hq] at hu
  nlinarith only [h,hr,show D.u-5+5=D.u by omega]

theorem wordVolume_q_five (hq : D.q=5) : 6*D.wordVolume+3*D.u≤D.u^2+20 := by
  have h := D.wordVolume_remainder_upper
  dsimp only at h
  rw [hq] at h
  norm_num only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceMul] at h
  have hb : (D.u-6)%3<3 := Nat.mod_lt _ (by decide)
  have hr : ((D.u-6)%3)*(3-(D.u-6)%3)≤2 := by
    interval_cases b : (D.u-6)%3 <;> norm_num
  have hu := D.q_add_one_le_u
  rw [hq] at hu
  nlinarith only [h,hr,show D.u-6+6=D.u by omega]

theorem wordVolume_q_six (hq : D.q=6) : 8*D.wordVolume+2*D.u≤D.u^2+25 := by
  have h := D.wordVolume_remainder_upper
  dsimp only at h
  rw [hq] at h
  norm_num only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceMul] at h
  have hb : (D.u-7)%4<4 := Nat.mod_lt _ (by decide)
  have hr : ((D.u-7)%4)*(4-(D.u-7)%4)≤4 := by
    interval_cases b : (D.u-7)%4 <;> norm_num
  have hu := D.q_add_one_le_u
  rw [hq] at hu
  nlinarith only [h,hr,show D.u-7+7=D.u by omega]

theorem wordVolume_q_seven (hq : D.q=7) : 8*D.wordVolume+4*D.u≤D.u^2+36 := by
  have h := D.wordVolume_remainder_upper
  dsimp only at h
  rw [hq] at h
  norm_num only [Nat.reduceAdd,Nat.reduceDiv,Nat.reduceMul] at h
  have hb : (D.u-8)%4<4 := Nat.mod_lt _ (by decide)
  have hr : ((D.u-8)%4)*(4-(D.u-8)%4)≤4 := by
    interval_cases b : (D.u-8)%4 <;> norm_num
  have hu := D.q_add_one_le_u
  rw [hq] at hu
  nlinarith only [h,hr,show D.u-8+8=D.u by omega]
end NSP14.Endpoint.Data
