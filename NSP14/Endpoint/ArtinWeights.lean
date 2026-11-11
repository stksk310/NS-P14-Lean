module
public import NSP14.Endpoint.FirstHarmonic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace NSP14.Endpoint

def weightedFirst (q N : ℕ) (h : ℕ → ℕ) : ℚ := (q:ℚ)+
  ∑ n∈Finset.range N,((q-1:ℕ):ℚ)*(h (n+1):ℚ)/(n+2)

/-- Arithmetic of the first harmonic row, stated in Q throughout. -/
theorem weightedFirst_third (q N P : ℕ) (h : ℕ → ℕ) (hq : 2≤q) (hN : 1≤N)
    (h1 : h 1=q) (hP : P=1+∑ n∈Finset.range N,h (n+1)) :
    weightedFirst q N h≤((q:ℚ)-1)*P/3+((q:ℚ)+1)*(q+2)/6 := by
  let a : ℚ := (q:ℚ)-1
  have ha : 0≤a := by
    have hqQ : (1:ℚ)≤(q:ℚ) := by exact_mod_cast (show (1:ℕ)≤q by omega)
    dsimp [a]
    linarith
  have hcast : ((q-1:ℕ):ℚ)=a := by dsimp [a];exact Nat.cast_sub (by omega)
  have hterm (n : ℕ) : a*(h (n+1):ℚ)/(n+2)≤a/3*(h (n+1):ℚ)+(if n=0 then a*q/6 else 0) := by
    by_cases hn : n=0
    · subst n
      simp only [h1,Nat.cast_zero,zero_add,ite_true]
      ring_nf
      exact le_rfl
    · rw [ite_eq_right hn,add_zero]
      have hd : (3:ℚ)≤(n:ℚ)+2 := by exact_mod_cast (show 3≤n+2 by omega)
      have hh : 0≤a*(h (n+1):ℚ) := mul_nonneg ha (Nat.cast_nonneg _)
      have hle := div_le_div_of_nonneg_left hh (by norm_num : (0:ℚ)<3) hd
      convert hle using 1; ring
  have hs := Finset.sum_le_sum (s:=Finset.range N) (fun n _ => hterm n)
  rw [Finset.sum_add_distrib,Finset.sum_ite_eq',ite_eq_left (Finset.mem_range.mpr (by omega : 0<N)),
    ←Finset.mul_sum] at hs
  have hPq : (P:ℚ)=1+∑ n∈Finset.range N,(h (n+1):ℚ) := by exact_mod_cast hP
  unfold weightedFirst
  simp_rw [hcast]
  dsimp [a] at hs hPq ⊢
  nlinarith

theorem weightedFirst_fourth (q N P : ℕ) (h : ℕ → ℕ) (hq : 2≤q) (hN : 2≤N)
    (h1 : h 1=q) (hP : P=1+∑ n∈Finset.range N,h (n+1)) :
    weightedFirst q N h≤((q:ℚ)-1)*P/4+((q:ℚ)+1)^2/4+((q:ℚ)-1)*h 2/12 := by
  let a : ℚ := (q:ℚ)-1
  have ha : 0≤a := by
    have hqQ : (1:ℚ)≤(q:ℚ) := by exact_mod_cast (show (1:ℕ)≤q by omega)
    dsimp [a]
    linarith
  have hcast : ((q-1:ℕ):ℚ)=a := by dsimp [a];exact Nat.cast_sub (by omega)
  have hterm (n : ℕ) : a*(h (n+1):ℚ)/(n+2)≤a/4*(h (n+1):ℚ)+
      (if n=0 then a*q/4 else 0)+(if n=1 then a*h 2/12 else 0) := by
    by_cases hn0 : n=0
    · subst n
      simp only [h1,Nat.cast_zero,zero_add,ite_true,show (0:ℕ)≠1 by decide,ite_false,add_zero]
      ring_nf
      exact le_rfl
    by_cases hn1 : n=1
    · subst n
      simp only [show (1:ℕ)≠0 by decide,ite_false,ite_true,add_zero]
      norm_num
      ring_nf
      exact le_rfl
    · rw [ite_eq_right hn0,ite_eq_right hn1,add_zero,add_zero]
      have hd : (4:ℚ)≤(n:ℚ)+2 := by exact_mod_cast (show 4≤n+2 by omega)
      have hh : 0≤a*(h (n+1):ℚ) := mul_nonneg ha (Nat.cast_nonneg _)
      have hle := div_le_div_of_nonneg_left hh (by norm_num : (0:ℚ)<4) hd
      convert hle using 1; ring
  have hs := Finset.sum_le_sum (s:=Finset.range N) (fun n _ => hterm n)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_range.mpr (by omega : 0<N)),ite_eq_left (Finset.mem_range.mpr (by omega : 1<N)),
    ←Finset.mul_sum] at hs
  have hPq : (P:ℚ)=1+∑ n∈Finset.range N,(h (n+1):ℚ) := by exact_mod_cast hP
  unfold weightedFirst
  simp_rw [hcast]
  dsimp [a] at hs hPq ⊢
  nlinarith

theorem weightedFirst_signed (q N P : ℕ) (h : ℕ → ℕ) (hq : 1≤q)
    (hP : P=1+∑ n∈Finset.range N,h (n+1)) :
    weightedFirst q N h-(P:ℚ)=(q:ℚ)-1+
      ∑ n∈Finset.range N,((q:ℚ)-(n+1)-2)*(h (n+1):ℚ)/(n+2) := by
  have hc : ((q-1:ℕ):ℚ)=(q:ℚ)-1 := Nat.cast_sub hq
  have hPq : (P:ℚ)=1+∑ n∈Finset.range N,(h (n+1):ℚ) := by exact_mod_cast hP
  have he (n : ℕ) : ((q:ℚ)-1)*(h (n+1):ℚ)/(n+2)-(h (n+1):ℚ)=
      ((q:ℚ)-(n+1)-2)*(h (n+1):ℚ)/(n+2) := by
    have hd : (n:ℚ)+2≠0 := by positivity
    field_simp
    ring
  unfold weightedFirst
  rw [hc,hPq]
  simp_rw [←he]
  rw [Finset.sum_sub_distrib]
  ring
end NSP14.Endpoint
namespace NSP14.Endpoint
open scoped BigOperators

theorem weightedFirst_five (N P : ℕ) (h : ℕ → ℕ) (hN : 2≤N)
    (h1 : h 1=5) (h2 : h 2≤15) (hP : P=1+∑ n∈Finset.range N,h (n+1)) :
    weightedFirst 5 N h-(P:ℚ)≤14 := by
  rw [weightedFirst_signed 5 N P h (by omega) hP]
  have hterm (n : ℕ) : ((5:ℚ)-(n+1)-2)*(h (n+1):ℚ)/(n+2)≤
      (if n=0 then (5:ℚ) else 0)+(if n=1 then (5:ℚ) else 0) := by
    by_cases hn0 : n=0
    · subst n
      norm_num [h1]
    by_cases hn1 : n=1
    · subst n
      have hh : (h 2:ℚ)≤15 := by exact_mod_cast h2
      norm_num
      linarith
    · rw [ite_eq_right hn0,ite_eq_right hn1,add_zero]
      apply div_nonpos_of_nonpos_of_nonneg
      · apply mul_nonpos_of_nonpos_of_nonneg
        · have hn : (2:ℚ)≤n := by exact_mod_cast (show 2≤n by omega)
          linarith
        · exact Nat.cast_nonneg _
      · positivity
  have hs := Finset.sum_le_sum (s:=Finset.range N) (fun n _ => hterm n)
  rw [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.sum_ite_eq',
    ite_eq_left (Finset.mem_range.mpr (by omega : 0<N)),ite_eq_left (Finset.mem_range.mpr (by omega : 1<N))] at hs
  norm_num
  linarith
end NSP14.Endpoint
