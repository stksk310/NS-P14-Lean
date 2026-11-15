module
public import NSP14.Homological.KoszulSlots
public import Mathlib.Data.Nat.Choose.Basic
@[expose] public section
open scoped Classical
namespace NSP14.Width

/-- Number of target wedges containing an entire block, with a genuine
negative-index guard rather than a saturated subtraction. -/
def containingBlock (r s j : ℕ) : ℕ := if r ≤ j then s.choose (j-r) else 0

def edgeCorrection (r s i : ℕ) : ℕ :=
  (if r ≤ i then (s+1).choose (i-r) else 0)+
  (if s ≤ i then (r+1).choose (i-s) else 0)

theorem choose_add_both_le (n k b : ℕ) : n.choose k ≤ (n+b).choose (k+b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ,Nat.add_succ,Nat.choose_succ_succ]
    omega

theorem choose_shift_le (n k a b : ℕ) (hb : b ≤ a) : n.choose k ≤ (n+a).choose (k+b) :=
  (choose_add_both_le n k b).trans (Nat.choose_le_choose _ (by omega))

theorem edge_summand_le (r s i c : ℕ) (hc : c ≤ r) :
    (if r ≤ i then (s+1).choose (i-r) else 0) ≤ (r+s+1).choose (i-c) := by
  split_ifs with hi
  · have h := choose_shift_le (s+1) (i-r) r (r-c) (by omega)
    convert h using 1; congr 1 <;> omega
  · exact Nat.zero_le _

theorem edgeCorrection_le_choose (r s i : ℕ) (_hr : 1 ≤ r) (hs : 1 ≤ s)
    (hi : 1 ≤ i) : edgeCorrection r s i ≤ (r+s+2).choose i := by
  have h1 := edge_summand_le r s i 0 (by omega)
  have h2 := edge_summand_le s r i 1 hs
  have hp := Nat.choose_succ_left (r+s+1) i (by omega)
  change (r+s+2).choose i=(r+s+1).choose (i-1)+(r+s+1).choose i at hp
  have he : s+r+1=r+s+1 := by omega
  rw [he] at h2
  simp only [Nat.sub_zero] at h1
  unfold edgeCorrection
  omega

theorem edgeCorrection_le_choose_pred (r s i : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hq : 3 ≤ r+s) (hi : 1 ≤ i) : edgeCorrection r s i ≤ (r+s+2).choose (i-1) := by
  by_cases hi1 : i=1
  · subst i
    unfold edgeCorrection
    by_cases hr1 : r=1 <;> by_cases hs1 : s=1
    · omega
    · simp [hr1,show ¬s ≤ 1 by omega]
    · simp [hs1,show ¬r ≤ 1 by omega]
    · simp [show ¬r ≤ 1 by omega,show ¬s ≤ 1 by omega]
  have hp := Nat.choose_succ_left (r+s+1) (i-1) (by omega)
  change (r+s+2).choose (i-1)=(r+s+1).choose (i-1-1)+(r+s+1).choose (i-1) at hp
  by_cases hr2 : 2 ≤ r
  · have h1 := edge_summand_le r s i 2 hr2
    have h2 := edge_summand_le s r i 1 hs
    rw [show s+r+1=r+s+1 by omega] at h2
    rw [show i-1-1=i-2 by omega] at hp
    unfold edgeCorrection
    omega
  · have hs2 : 2 ≤ s := by omega
    have h1 := edge_summand_le r s i 1 hr
    have h2 := edge_summand_le s r i 2 hs2
    rw [show s+r+1=r+s+1 by omega] at h2
    rw [show i-1-1=i-2 by omega] at hp
    unfold edgeCorrection
    omega
end NSP14.Width

namespace NSP14.Width
theorem edge_base_identity (q i : ℕ) (hi : 1 ≤ i) :
    i*(q+2).choose (i+1)+3*q.choose i+2*q.choose (i-1)+q.choose (i+1)=
      (q+3)*(q.choose i+q.choose (i-1)) := by
  have hp := Nat.choose_succ_left q i (by omega)
  have hp1 := Nat.choose_succ_succ q i
  have hp2 := Nat.choose_succ_succ (q+1) i
  change (q+1).choose (i+1)=q.choose i+q.choose (i+1) at hp1
  change (q+2).choose (i+1)=(q+1).choose i+(q+1).choose (i+1) at hp2
  have h := Nat.add_one_mul_choose_eq (q+1) i
  change (q+2)*(q+1).choose i=(q+2).choose (i+1)*(i+1) at h
  have hf : (q+2).choose (i+1)=q.choose (i-1)+2*q.choose i+q.choose (i+1) := by
    rw [hp2,hp,hp1]
    omega
  rw [hp,hf] at h
  nlinarith only [h,hf]

def edgeTopCorrection (q i : ℕ) : ℕ := if i=q ∨ i=q+1 then 1 else 0

theorem edgeCorrection_zero_left (q i : ℕ) :
    edgeCorrection 0 q i=(q+1).choose i+edgeTopCorrection q i := by
  unfold edgeCorrection edgeTopCorrection
  simp only [Nat.zero_le,ite_true,Nat.sub_zero,Nat.zero_add]
  by_cases hqi : q ≤ i
  · rw [ite_eq_left hqi]
    by_cases hiq : i=q
    · subst i
      simp
    · by_cases hiq1 : i=q+1
      · subst i
        simp
      · rw [Nat.choose_eq_zero_of_lt (n:=1) (k:=i-q) (by omega),ite_eq_right (by omega),add_zero]
  · rw [ite_eq_right hqi,ite_eq_right (by omega),add_zero]

theorem edgeCorrection_comm (r s i : ℕ) : edgeCorrection r s i=edgeCorrection s r i := by
  unfold edgeCorrection
  omega

theorem edgeTopCorrection_le (q i : ℕ) (_hq : 3 ≤ q) (hi : 1 ≤ i) :
    edgeTopCorrection q i ≤ min ((q+2).choose (i-1)) ((q+2).choose i) := by
  unfold edgeTopCorrection
  split_ifs with he
  · have hiq : i ≤ q+1 := by omega
    apply Nat.le_min.mpr
    constructor
    · exact Nat.choose_pos (by omega)
    · exact Nat.choose_pos (by omega)
  · exact Nat.zero_le _
end NSP14.Width
