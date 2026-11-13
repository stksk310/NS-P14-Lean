module
public import NSP14.Width.NormalizedCapacity
public import NSP14.Width.SparseFirst
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

/-- Additive, kernel-compensated resource inequality; subtraction is never truncated. -/
theorem actual_sparse_resource_add (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.Variables (D.fullG k) i+D.u*(D.q+1).choose (i-1)+
      (D.q+1).choose (i+1)≤D.wordVolume*(D.q+2).choose i := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  have h := D.actual_positive_rows_add k (j+1) (by omega)
  have hP := Nat.mul_le_mul_right ((D.q+1).choose (j+1)) (D.coreP_le_wordVolume k)
  have hR : D.Rhat+D.u≤D.wordVolume := by
    have hu := D.wordVolume_ge_u
    have hr : D.Rhat≤D.wordVolume-D.u := min_le_left _ _
    omega
  have hRs := Nat.mul_le_mul_right ((D.q+1).choose j) hR
  simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel] at h ⊢
  rw [Nat.choose_succ_succ (D.q+1) j]
  nlinarith only [h,hP,hRs]

/-- Second-row payment and normalized capacities pay every row through the top row e. -/
theorem actual_sparse_higher (he : 6≤D.q+2) (hu : 2*(D.q+2)-2≤D.u)
    (i : ℕ) (hi : 2 ≤ i) (hie : i≤D.q+2) :
    totalBetti k D.Variables (D.fullG k) i≤ i*D.u.choose (i+1) := by
  let e := D.q+2
  have hue : e≤D.u := by dsimp [e];omega
  have hW : ((e:ℚ)-1)*D.wordVolume≤(D.u:ℚ)^2 := by
    have h : ((D.q:ℚ)+1)*D.wordVolume≤(D.u:ℚ)^2 := by exact_mod_cast D.wordVolume_quadratic_bound
    dsimp [e]
    push_cast
    nlinarith only [h]
  have hp := NSP14.Width.sparse_second_payment e D.u he hu (D.wordVolume:ℚ) hW
  have hepos : (0:ℚ)<(e.choose 2:ℚ) := by exact_mod_cast Nat.choose_pos (by dsimp [e];omega : 2≤e)
  have hcap2 : (D.wordVolume:ℚ)≤NSP14.Width.normalizedCapacity e D.u 2 := by
    unfold NSP14.Width.normalizedCapacity
    apply (le_div_iff₀ hepos).mpr
    simpa only [Nat.reduceAdd,Nat.reduceSub,Nat.choose_one_right,Nat.cast_ofNat,
      Nat.cast_sub (by dsimp [e];omega : 1≤e),Nat.cast_one] using hp
  have hcap := hcap2.trans (NSP14.Width.normalized_capacity_monotone e D.u i hue hi hie)
  have heipos : (0:ℚ)<(e.choose i:ℚ) := by exact_mod_cast Nat.choose_pos hie
  have hpay := (le_div_iff₀ heipos).mp hcap
  have h := D.actual_sparse_resource_add k i (by omega)
  have hQ : (totalBetti k D.Variables (D.fullG k) i:ℚ)+(D.u:ℚ)*((D.q+1).choose (i-1):ℚ)+
      ((D.q+1).choose (i+1):ℚ)≤(D.wordVolume:ℚ)*((D.q+2).choose i:ℚ) := by exact_mod_cast h
  have hem : e-1=D.q+1 := by rfl
  rw [hem] at hpay
  change (D.wordVolume:ℚ)*((D.q+2).choose i:ℚ)≤_ at hpay
  have hresult : (totalBetti k D.Variables (D.fullG k) i:ℚ)≤(i:ℚ)*(D.u.choose (i+1):ℚ) := by
    linarith only [hQ,hpay]
  exact_mod_cast hresult
end NSP14.Endpoint.Data
