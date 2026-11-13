module
public import NSP14.Width.SparseSecond
@[expose] public section
open scoped BigOperators
namespace NSP14.Width

def chooseRatio (e u i : ℕ) : ℚ := (u.choose i:ℚ)/(e.choose i:ℚ)

def normalizedCapacity (e u i : ℕ) : ℚ :=
  ((i:ℚ)*(u.choose (i+1):ℚ)+(u:ℚ)*((e-1).choose (i-1):ℚ)+
    ((e-1).choose (i+1):ℚ))/(e.choose i:ℚ)

theorem lower_choose_fraction (e i : ℕ) (hi : 1≤ i) (hie : i≤e) :
    (((e-1).choose (i-1):ℚ))/(e.choose i:ℚ)=(i:ℚ)/e := by
  have he : 1≤e := hi.trans hie
  have h := Nat.add_one_mul_choose_eq (e-1) (i-1)
  rw [Nat.sub_add_cancel he,Nat.sub_add_cancel hi] at h
  have hQ : (e:ℚ)*((e-1).choose (i-1):ℚ)=(e.choose i:ℚ)*(i:ℚ) := by exact_mod_cast h
  have hc : (e.choose i:ℚ)≠0 := by exact_mod_cast (Nat.choose_ne_zero hie)
  have heQ : (e:ℚ)≠0 := by exact_mod_cast (show e≠0 by omega)
  field_simp
  nlinarith only [hQ]

/-- For u>=e the binomial ratio is nondecreasing in its lower index, including i+1=e. -/
theorem chooseRatio_adj (e u i : ℕ) (hu : e≤u) (hi : i<e) :
    chooseRatio e u i≤chooseRatio e u (i+1) := by
  have hc : (0:ℚ)<(e.choose i:ℚ) := by exact_mod_cast Nat.choose_pos (by omega : i≤e)
  have hc' : (0:ℚ)<(e.choose (i+1):ℚ) := by exact_mod_cast Nat.choose_pos (by omega : i+1≤e)
  have hU : (u.choose (i+1):ℚ)*((i:ℚ)+1)=(u.choose i:ℚ)*((u:ℚ)-i) := by
    have h := Nat.choose_succ_right_eq u i
    have hQ : (u.choose (i+1):ℚ)*((i:ℚ)+1)=(u.choose i:ℚ)*((u-i:ℕ):ℚ) := by exact_mod_cast h
    rwa [Nat.cast_sub (by omega : i≤u)] at hQ
  have hE : (e.choose (i+1):ℚ)*((i:ℚ)+1)=(e.choose i:ℚ)*((e:ℚ)-i) := by
    have h := Nat.choose_succ_right_eq e i
    have hQ : (e.choose (i+1):ℚ)*((i:ℚ)+1)=(e.choose i:ℚ)*((e-i:ℕ):ℚ) := by exact_mod_cast h
    rwa [Nat.cast_sub (by omega : i≤e)] at hQ
  have huQ : (e:ℚ)≤u := by exact_mod_cast hu
  have hnonneg : 0≤(u.choose i:ℚ)*(e.choose i:ℚ)*((u:ℚ)-e) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (by linarith)
  have hUs := congrArg (fun x : ℚ => x*(e.choose i:ℚ)) hU
  have hEs := congrArg (fun x : ℚ => x*(u.choose i:ℚ)) hE
  unfold chooseRatio
  apply (div_le_div_iff₀ hc hc').mpr
  apply (mul_le_mul_iff_left₀ (show (0:ℚ)<(i:ℚ)+1 by positivity)).mp
  nlinarith only [hUs,hEs,hnonneg]

theorem capacity_increment_adj (e u i : ℕ) (hu : e≤u) (hi : i<e) :
    (i:ℚ)*chooseRatio e u i+(i:ℚ)/e≤
      ((i:ℚ)+1)*chooseRatio e u (i+1)+((i:ℚ)+1)/e := by
  have hratio := chooseRatio_adj e u i hu hi
  have he : (0:ℚ)≤e := Nat.cast_nonneg _
  apply add_le_add
  · exact mul_le_mul (show (i:ℚ)≤(i:ℚ)+1 by linarith) hratio
      (by unfold chooseRatio;positivity) (by positivity)
  · exact div_le_div_of_nonneg_right (show (i:ℚ)≤(i:ℚ)+1 by linarith) he

theorem normalized_capacity_step (e u i : ℕ) (hi : 1≤ i) (hie : i≤e) :
    normalizedCapacity e (u+1) i=normalizedCapacity e u i+
      (i:ℚ)*chooseRatio e u i+(i:ℚ)/e := by
  have hfrac := lower_choose_fraction e i hi hie
  unfold normalizedCapacity chooseRatio
  rw [Nat.choose_succ_succ']
  push_cast
  rw [←hfrac]
  ring

theorem normalized_capacity_base (e i : ℕ) (hi : 1≤ i) (hie : i≤e) :
    normalizedCapacity e e i=(e:ℚ)-1+(i:ℚ)/e := by
  have he : 1≤e := hi.trans hie
  have hfrac := lower_choose_fraction e i hi hie
  have hc : (e.choose i:ℚ)≠0 := by exact_mod_cast Nat.choose_ne_zero hie
  have heQ : ((e-1:ℕ):ℚ)=(e:ℚ)-1 := Nat.cast_sub he
  have hnum : (i:ℚ)*(e.choose (i+1):ℚ)+(e:ℚ)*((e-1).choose (i-1):ℚ)+
      ((e-1).choose (i+1):ℚ)=((e:ℚ)-1)*(e.choose i:ℚ)+((e-1).choose (i-1):ℚ) := by
    by_cases hitop : i=e
    · subst i
      simp only [Nat.choose_succ_self,Nat.choose_self,Nat.cast_zero,Nat.cast_one,mul_zero,mul_one]
      have hsub : e-1<e+1 := by omega
      rw [Nat.choose_eq_zero_of_lt hsub]
      norm_num

    · have hsmall : i≤e-1 := by omega
      have hPas := Nat.choose_succ_succ' (e-1) i
      have hPas' := Nat.choose_succ_succ' (e-1) (i-1)
      rw [Nat.sub_add_cancel he] at hPas hPas'
      rw [Nat.sub_add_cancel hi] at hPas'
      have hAdj := Nat.choose_succ_right_eq (e-1) i
      have hp : (e.choose (i+1):ℚ)=((e-1).choose i:ℚ)+((e-1).choose (i+1):ℚ) := by exact_mod_cast hPas
      have hp' : (e.choose i:ℚ)=((e-1).choose (i-1):ℚ)+((e-1).choose i:ℚ) := by exact_mod_cast hPas'
      have ha : ((e-1).choose (i+1):ℚ)*((i:ℚ)+1)=
          ((e-1).choose i:ℚ)*((e:ℚ)-1-i) := by
        have h : ((e-1).choose (i+1):ℚ)*((i:ℚ)+1)=
            ((e-1).choose i:ℚ)*((e-1-i:ℕ):ℚ) := by exact_mod_cast hAdj
        rwa [Nat.cast_sub hsmall,heQ] at h
      nlinarith only [hp,hp',ha]
  unfold normalizedCapacity
  rw [hnum,←hfrac]
  field_simp

theorem normalized_capacity_adj (e u i : ℕ) (hu : e≤u) (hi : 1≤ i) (hie : i<e) :
    normalizedCapacity e u i≤normalizedCapacity e u (i+1) := by
  induction u,hu using Nat.le_induction with
  | base =>
    rw [normalized_capacity_base e i hi (by omega),normalized_capacity_base e (i+1) (by omega) (by omega)]
    push_cast
    have he : (0:ℚ)<e := by exact_mod_cast (show 0<e by omega)
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (show (i:ℚ)≤(i:ℚ)+1 by linarith) he.le
  | succ u hu ih =>
    rw [normalized_capacity_step e u i hi (by omega),normalized_capacity_step e u (i+1) (by omega) (by omega)]
    have h := capacity_increment_adj e u i hu hie
    push_cast
    linarith

/-- All rows 2..e, with no division by e-i at the top row. -/
theorem normalized_capacity_monotone (e u i : ℕ) (hu : e≤u) (hi : 2≤ i) (hie : i≤e) :
    normalizedCapacity e u 2≤normalizedCapacity e u i := by
  suffices h : ∀ j : ℕ, 2≤j → j≤e → normalizedCapacity e u 2≤normalizedCapacity e u j from h i hi hie
  intro j hj
  induction j,hj using Nat.le_induction with
  | base => intro _;rfl
  | succ j hj ih =>
    intro hje
    exact (ih (by omega)).trans (normalized_capacity_adj e u j hu (by omega) (by omega))
end NSP14.Width
