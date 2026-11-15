module
import NSP14.NarrowFour.CubicPayment
open NSP14 NSP14.NarrowFour
example (z : ℕ) :
    12*((2:ℚ)*((6+z).choose 3:ℚ)-(5*((6+z:ℕ):ℚ)^2/4-2*((6+z:ℕ):ℚ)+4))=
      4*(z:ℚ)^3+45*(z:ℚ)^2+140*(z:ℚ)+36 := cubic_gap z
example : (T 2 6,T 3 6,T 4 6)=(40,45,24) := by norm_num [T,Nat.choose]
example : (U2 6,U3 6,U4 6)=(37,22,4) := by norm_num [U2,U3,U4]
example : 12*(T 2 6-U2 6)=36 := by norm_num [T,U2,Nat.choose]
example (u : ℕ) (hu : 6≤u) : U2 u<T 2 u ∧ U3 u≤T 3 u ∧ U4 u≤T 4 u :=
  ⟨second_payment u hu,third_payment u hu,fourth_payment u hu⟩
example (u : ℕ) : 8*T 3 u=3*((u:ℚ)-3)*T 2 u := ratio_three u
example (u : ℕ) : 10*T 4 u=((u:ℚ)-3)*((u:ℚ)-4)*T 2 u := ratio_four u
example (u : ℕ) (hu : 6≤u) : T 2 u≤T 3 u ∧ T 2 u≤5*T 4 u :=
  ⟨second_le_third u hu,second_le_five_fourth u hu⟩
