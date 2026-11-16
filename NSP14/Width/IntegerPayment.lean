module
public import NSP14.Width.FirstResources
@[expose] public section
namespace NSP14.Width

/-- Integer slack closes the antipodal first row uniformly from h = 4 onward.
All divisions and polynomial comparisons take place over the rationals. -/
theorem antipodal_integer_payment (h b : ℕ) (hh : 4 ≤ h)
    (hb : (6:ℚ)*b+7*h ≤ 11*(h:ℚ)^2+30) :
    b ≤ (2*h).choose 2+1 := by
  by_contra hn
  have hnext : (2*h).choose 2+2 ≤ b := by omega
  have hnextQ : ((2*h).choose 2:ℚ)+2 ≤ b := by exact_mod_cast hnext
  have hhQ : (4:ℚ) ≤ h := by exact_mod_cast hh
  have hc := choose_two_rat (2*h)
  push_cast at hc
  nlinarith only [hb,hnextQ,hhQ,hc,sq_nonneg ((h:ℚ)-4)]

/-- Integer slack closes every non-antipodal first row from u = 8 onward. -/
theorem nonAntipodal_integer_payment (u b : ℕ) (hu : 8 ≤ u)
    (hb : (12:ℚ)*b+7*u ≤ 5*(u:ℚ)^2+90) :
    b ≤ u.choose 2+1 := by
  by_contra hn
  have hnext : u.choose 2+2 ≤ b := by omega
  have hnextQ : (u.choose 2:ℚ)+2 ≤ b := by exact_mod_cast hnext
  have huQ : (8:ℚ) ≤ u := by exact_mod_cast hu
  have hc := choose_two_rat u
  nlinarith only [hb,hnextQ,huQ,hc,sq_nonneg ((u:ℚ)-8)]

end NSP14.Width
