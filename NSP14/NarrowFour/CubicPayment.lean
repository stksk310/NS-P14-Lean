module
public import NSP14.Width.SparseSecond
@[expose] public section
namespace NSP14.NarrowFour

/-- The V06 rational envelopes, before any physical target is chosen. -/
def U2 (u : ℕ) : ℚ := 5*(u:ℚ)^2/4-2*u+4
def U3 (u : ℕ) : ℚ := (u:ℚ)^2-3*u+4
def U4 (u : ℕ) : ℚ := (u:ℚ)^2/4-u+1
def T (i u : ℕ) : ℚ := (i:ℚ)*(u.choose (i+1):ℚ)

theorem choose_four_rat (u : ℕ) :
    (u.choose 4:ℚ)=(u:ℚ)*((u:ℚ)-1)*((u:ℚ)-2)*((u:ℚ)-3)/24 := by
  cases u with
  | zero => norm_num
  | succ n =>
    have hn := Nat.add_one_mul_choose_eq n 3
    have h : ((n:ℚ)+1)*(n.choose 3:ℚ)=((n+1).choose 4:ℚ)*4 := by exact_mod_cast hn
    rw [Width.choose_three_rat] at h
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith only [h]

theorem choose_five_rat (u : ℕ) :
    (u.choose 5:ℚ)=(u:ℚ)*((u:ℚ)-1)*((u:ℚ)-2)*((u:ℚ)-3)*((u:ℚ)-4)/120 := by
  cases u with
  | zero => norm_num
  | succ n =>
    have hn := Nat.add_one_mul_choose_eq n 4
    have h : ((n:ℚ)+1)*(n.choose 4:ℚ)=((n+1).choose 5:ℚ)*5 := by exact_mod_cast hn
    rw [choose_four_rat] at h
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith only [h]

/-- Exact new V06 cubic; in particular the constant is 36 and the linear coefficient 140. -/
theorem cubic_gap (z : ℕ) :
    12*((2:ℚ)*((6+z).choose 3:ℚ)-(5*((6+z:ℕ):ℚ)^2/4-2*((6+z:ℕ):ℚ)+4))=
      4*(z:ℚ)^3+45*(z:ℚ)^2+140*(z:ℚ)+36 := by
  rw [Width.choose_three_rat]
  push_cast
  ring

theorem second_payment (u : ℕ) (hu : 6≤u) : U2 u<T 2 u := by
  obtain ⟨z,rfl⟩ := Nat.exists_eq_add_of_le hu
  have h := cubic_gap z
  have hp : (0:ℚ)<4*(z:ℚ)^3+45*(z:ℚ)^2+140*(z:ℚ)+36 := by positivity
  dsimp [U2,T]
  nlinarith only [h,hp]

theorem envelope_three (u : ℕ) : U2 u-U3 u=(u:ℚ)^2/4+u := by
  dsimp [U2,U3];ring

theorem envelope_four (u : ℕ) : U2 u-5*U4 u=3*(u:ℚ)-1 := by
  dsimp [U2,U4];ring

theorem ratio_three (u : ℕ) : 8*T 3 u=3*((u:ℚ)-3)*T 2 u := by
  dsimp [T]
  rw [Width.choose_three_rat,choose_four_rat]
  ring

theorem ratio_four (u : ℕ) : 10*T 4 u=((u:ℚ)-3)*((u:ℚ)-4)*T 2 u := by
  dsimp [T]
  rw [Width.choose_three_rat,choose_five_rat]
  ring

theorem second_le_third (u : ℕ) (hu : 6≤u) : T 2 u≤T 3 u := by
  have h := ratio_three u
  have hn : 0≤T 2 u := by dsimp [T];positivity
  have huq : (6:ℚ)≤u := by exact_mod_cast hu
  have hp := mul_nonneg (show 0≤3*((u:ℚ)-3)-8 by linarith only [huq]) hn
  nlinarith only [h,hp]

theorem second_le_five_fourth (u : ℕ) (hu : 6≤u) : T 2 u≤5*T 4 u := by
  have h := ratio_four u
  have hn : 0≤T 2 u := by dsimp [T];positivity
  have huq : (6:ℚ)≤u := by exact_mod_cast hu
  have hb : 0≤((u:ℚ)-3)*((u:ℚ)-4)-2 := by nlinarith only [huq]
  have hp := mul_nonneg hb hn
  nlinarith only [h,hp]

theorem third_payment (u : ℕ) (hu : 6≤u) : U3 u≤T 3 u := by
  have h := second_payment u hu
  have he := envelope_three u
  have hp : (0:ℚ)≤(u:ℚ)^2/4+u := by positivity
  have ht := second_le_third u hu
  linarith only [h,he,hp,ht]

theorem fourth_payment (u : ℕ) (hu : 6≤u) : U4 u≤T 4 u := by
  have h := second_payment u hu
  have he := envelope_four u
  have hp : (6:ℚ)≤u := by exact_mod_cast hu
  have ht := second_le_five_fourth u hu
  linarith only [h,he,hp,ht]

end NSP14.NarrowFour
