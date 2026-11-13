module
public import NSP14.Width.FirstResources
@[expose] public section
namespace NSP14.Width

theorem choose_three_rat (u : ℕ) :
    (u.choose 3:ℚ)=(u:ℚ)*((u:ℚ)-1)*((u:ℚ)-2)/6 := by
  cases u with
  | zero => norm_num
  | succ n =>
    have hn := Nat.add_one_mul_choose_eq n 2
    have h : ((n:ℚ)+1)*(n.choose 2:ℚ)=((n+1).choose 3:ℚ)*3 := by exact_mod_cast hn
    rw [choose_two_rat] at h
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith only [h]

/-- Second-row payment; e=7 and e>=8 share one manifestly positive polynomial. -/
theorem sparse_second_payment (e u : ℕ) (he : 6≤e) (hu : 2*e-2≤u)
    (W : ℚ) (hW : ((e:ℚ)-1)*W≤(u:ℚ)^2) :
    W*(e.choose 2:ℚ)≤2*(u.choose 3:ℚ)+(u:ℚ)*(e-1)+( (e-1).choose 3:ℚ) := by
  have heQ : (6:ℚ)≤e := by exact_mod_cast he
  have huQ : 2*(e:ℚ)-2≤u := by
    have h : 2*(e:ℚ)≤(u:ℚ)+2 := by exact_mod_cast (show 2*e≤u+2 by omega)
    linarith only [h]
  have hws := mul_le_mul_of_nonneg_left hW (show 0≤(e:ℚ)/2 by positivity)
  have hgap : (e:ℚ)*(u:ℚ)^2/2≤
      2*(u.choose 3:ℚ)+(u:ℚ)*(e-1)+((e-1).choose 3:ℚ) := by
    by_cases h6 : e=6
    · subst e
      norm_num only [Nat.cast_ofNat,Nat.reduceSub] at huQ ⊢
      rw [show (5:ℕ).choose 3=10 by decide]
      norm_num only [Nat.cast_ofNat]
      have hp : 0≤((u:ℚ)-10)*((u:ℚ)-3)*((u:ℚ)+1) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
      rw [choose_three_rat]
      nlinarith only [hp]
    · have he7 : (7:ℚ)≤e := by exact_mod_cast (show 7≤e by omega)
      let v : ℚ := (e:ℚ)-7
      let z : ℚ := (u:ℚ)-(2*(e:ℚ)-2)
      have hv : 0≤v := by dsimp [v];linarith only [he7]
      have hz : 0≤z := by dsimp [z];linarith only [huQ]
      have hid : 2*(u:ℚ)^2-(3*(e:ℚ)+6)*u+6*(e:ℚ)-2=
          2*v^2+5*v*z+12*v+2*z^2+21*z+4 := by dsimp [v,z];ring
      have hpos : 0≤2*(u:ℚ)^2-(3*(e:ℚ)+6)*u+6*(e:ℚ)-2 := by
        rw [hid]
        positivity
      have hprod := mul_nonneg (show (0:ℚ)≤u by positivity) hpos
      have hc : (0:ℚ)≤((e-1).choose 3:ℚ) := Nat.cast_nonneg _
      rw [choose_three_rat]
      nlinarith only [hprod,hc]
  rw [choose_two_rat]
  nlinarith only [hws,hgap]
end NSP14.Width
