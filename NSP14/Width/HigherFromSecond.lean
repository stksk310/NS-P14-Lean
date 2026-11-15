module
public import NSP14.Width.NormalizedCapacity
public import NSP14.Endpoint.PositiveRows
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.Width

/-- Payment of one rational resource envelope in row two pays every row up to e.
Only the positive binomial coefficient is divided out, including in the top row. -/
theorem higher_capacity_from_second (e u : ℕ) (B : ℚ) (he : 2 ≤ e) (hu : e ≤ u)
    (hsecond : B*(e.choose 2:ℚ) ≤ 2*(u.choose 3:ℚ)+(u:ℚ)*(e-1)+
      ((e-1).choose 3:ℚ)) (i : ℕ) (hi : 2 ≤ i) (hie : i ≤ e) :
    B*(e.choose i:ℚ) ≤ (i:ℚ)*(u.choose (i+1):ℚ)+
      (u:ℚ)*((e-1).choose (i-1):ℚ)+((e-1).choose (i+1):ℚ) := by
  have hc2 : (0:ℚ) < (e.choose 2:ℚ) := by exact_mod_cast Nat.choose_pos he
  have hcap2 : B ≤ normalizedCapacity e u 2 := by
    unfold normalizedCapacity
    apply (le_div_iff₀ hc2).mpr
    simpa only [Nat.reduceAdd,Nat.reduceSub,Nat.choose_one_right,Nat.cast_ofNat,
      Nat.cast_sub (by omega : 1 ≤ e),Nat.cast_one] using hsecond
  have hcap := hcap2.trans (normalized_capacity_monotone e u i hu hi hie)
  have hci : (0:ℚ) < (e.choose i:ℚ) := by exact_mod_cast Nat.choose_pos hie
  exact (le_div_iff₀ hci).mp hcap
end NSP14.Width
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

/-- The same rational envelope bounds both core resources in the additive row package. -/
theorem actual_resource_envelope_add (B : ℚ) (hP : (D.coreP k:ℚ) ≤ B)
    (hR : (D.Rhat:ℚ)+D.u ≤ B) (i : ℕ) (hi : 1 ≤ i) :
    (totalBetti k D.Variables (D.fullG k) i:ℚ)+
      (D.u:ℚ)*((D.q+1).choose (i-1):ℚ)+((D.q+1).choose (i+1):ℚ) ≤
      B*((D.q+2).choose i:ℚ) := by
  have h := D.actual_positive_rows_add k i hi
  have hQ : (totalBetti k D.Variables (D.fullG k) i:ℚ)+
      ((D.q+1).choose (i+1):ℚ) ≤
      (D.coreP k:ℚ)*((D.q+1).choose i:ℚ)+
        (D.Rhat:ℚ)*((D.q+1).choose (i-1):ℚ) := by exact_mod_cast h
  have hp := mul_le_mul_of_nonneg_right hP
    (show (0:ℚ) ≤ ((D.q+1).choose i:ℚ) by positivity)
  have hr := mul_le_mul_of_nonneg_right hR
    (show (0:ℚ) ≤ ((D.q+1).choose (i-1):ℚ) by positivity)
  have hpas := Nat.choose_succ_succ (D.q+1) (i-1)
  simp only [Nat.succ_eq_add_one,Nat.sub_add_cancel hi] at hpas
  have hpasQ : ((D.q+2).choose i:ℚ)=
      ((D.q+1).choose (i-1):ℚ)+((D.q+1).choose i:ℚ) := by exact_mod_cast hpas
  rw [hpasQ]
  nlinarith only [hQ,hp,hr]

/-- A row-two payment for the resource envelope gives all actual higher rows.
The field is arbitrary; every resource division is in the rationals. -/
theorem actual_higher_from_second (B : ℚ) (hP : (D.coreP k:ℚ) ≤ B)
    (hR : (D.Rhat:ℚ)+D.u ≤ B) (hu : D.q+2 ≤ D.u)
    (hsecond : B*((D.q+2).choose 2:ℚ) ≤
      2*(D.u.choose 3:ℚ)+(D.u:ℚ)*(D.q+1)+((D.q+1).choose 3:ℚ))
    (i : ℕ) (hi : 2 ≤ i) (hie : i ≤ D.q+2) :
    totalBetti k D.Variables (D.fullG k) i ≤ i*D.u.choose (i+1) := by
  have hem : D.q+2-1=D.q+1 := by omega
  have hs : B*((D.q+2).choose 2:ℚ) ≤
      2*(D.u.choose 3:ℚ)+(D.u:ℚ)*((D.q+2:ℕ)-1)+
        ((D.q+2-1).choose 3:ℚ) := by
    rw [hem]
    push_cast
    linarith only [hsecond]
  have hpay := NSP14.Width.higher_capacity_from_second (D.q+2) D.u B
    (by omega) hu hs i hi hie
  have h := D.actual_resource_envelope_add k B hP hR i (by omega)
  rw [hem] at hpay
  have hresult : (totalBetti k D.Variables (D.fullG k) i:ℚ) ≤
      (i:ℚ)*(D.u.choose (i+1):ℚ) := by linarith only [h,hpay]
  exact_mod_cast hresult
end NSP14.Endpoint.Data
