module
public import NSP14.ArithmeticSequence.ModelCoordinates
@[expose] public section
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

def residueDefect : ℕ := D.v-((D.m-1)%D.v)

theorem residueDefect_pos : 1 ≤ D.residueDefect := by
  have h := Nat.mod_lt (D.m-1) (show 0 < D.v from D.v_pos)
  unfold residueDefect
  omega

theorem residueDefect_le : D.residueDefect ≤ D.v := Nat.sub_le _ _

theorem residueDefect_complement : D.v-D.residueDefect=(D.m-1)%D.v := by
  have h := Nat.mod_lt (D.m-1) (show 0 < D.v from D.v_pos)
  unfold residueDefect
  omega

theorem blockCount_add_multiple (i q : ℕ) : D.blockCount (i+q*D.v)=D.blockCount i+q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.add_mul,Nat.one_mul,← Nat.add_assoc,D.blockCount_add_v,ih]
    omega

theorem window_blockCount (n : ℕ) (hn : n < D.v) :
    D.blockCount (D.m+n)=(D.m-1)/D.v+(if n<D.residueDefect then 1 else 2) := by
  let r := (D.m-1)%D.v
  let q := (D.m-1)/D.v
  have hr : r < D.v := Nat.mod_lt _ (show 0 < D.v from D.v_pos)
  have hm : D.m=r+q*D.v+1 := by
    have h := Nat.mod_add_div (D.m-1) D.v
    change r+D.v*q=D.m-1 at h
    have hm := Nat.sub_add_cancel (show 1 ≤ D.m by have := D.m_two;omega)
    nlinarith only [h,hm]
  have he : D.m+n=(r+1+n)+q*D.v := by omega
  rw [he,D.blockCount_add_multiple]
  by_cases hc : n < D.residueDefect
  · rw [ite_eq_left hc]
    have hl : D.blockCount (r+1+n) ≤ 1 := (D.blockCount_le_iff _ _).mpr (by
      have h : n < D.v-r := hc
      omega)
    have hp := D.blockCount_pos (show 0 < r+1+n by omega)
    change D.blockCount (r+1+n)+q=q+1
    omega
  · rw [ite_eq_right hc]
    have hl : D.blockCount (r+1+n) ≤ 2 := (D.blockCount_le_iff _ _).mpr (by nlinarith)
    have hp : 1 < D.blockCount (r+1+n) := by
      by_contra hp
      have hle : D.blockCount (r+1+n) ≤ 1 := by omega
      have h := (D.blockCount_le_iff (r+1+n) 1).mp hle
      have hc' : D.v-r ≤ n := by have hc' : ¬n<D.v-r := hc;omega
      have hs := Nat.sub_add_cancel (show r ≤ D.v from hr.le)
      nlinarith only [h,hc',hs]
    change D.blockCount (r+1+n)+q=q+2
    omega
end NSP14.ArithmeticSequence.Data
