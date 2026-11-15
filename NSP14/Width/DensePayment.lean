module
public import NSP14.Width.NormalizedCapacity
@[expose] public section
open scoped Classical BigOperators
open CategoryTheory CategoryTheory.Limits NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Width

theorem choose_add_one_term (n t j : ℕ) :
    n.choose (j+1)+t*n.choose j≤(n+t).choose (j+1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hp : (n+(t+1)).choose (j+1)=(n+t).choose j+(n+t).choose (j+1) := by
      rw [Nat.add_succ,Nat.choose_succ_succ]
    rw [hp]
    have hm := Nat.choose_le_choose j (show n≤n+t by omega)
    nlinarith only [ih,hm]

theorem choose_add_two_terms (n t j : ℕ) :
    n.choose (j+2)+t*n.choose (j+1)+t.choose 2*n.choose j≤(n+t).choose (j+2) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hp : (n+(t+1)).choose (j+2)=(n+t).choose (j+1)+(n+t).choose (j+2) := by
      simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using Nat.choose_succ_succ (n+t) (j+1)
    have hc : (t+1).choose 2=t+t.choose 2 := by
      simpa only [Nat.choose_one_right] using Nat.choose_succ_succ t 1
    rw [hp,hc]
    have hm := choose_add_one_term n t j
    nlinarith only [ih,hm]

/-- The V06 rational coefficient is nonnegative, including q = 4, t = 3. -/
theorem dense_gamma_nonneg (q t : ℕ) (hq : 4≤q) (ht : 3≤t) (htq : t≤q) :
    0 ≤ (5*(t:ℚ)^2-17*(t:ℚ)-6)/6+((t:ℚ)-1)*((q:ℚ)-(t:ℚ)) := by
  have hqQ : (4:ℚ)≤q := by exact_mod_cast hq
  have htQ : (3:ℚ)≤t := by exact_mod_cast ht
  have htqQ : (t:ℚ)≤q := by exact_mod_cast htq
  have hprod : 0≤((t:ℚ)-3)*((q:ℚ)-(t:ℚ)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith only [hqQ, htQ, hprod, sq_nonneg ((t:ℚ)-3)]

/-- Unified coefficient comparison for the whole t ≥ 3 branch. -/
theorem dense_coeff_ge_three (q t K c : ℕ) (hq : 4≤q) (ht : 3≤t) (htq : t≤q)
    (hK : 3*K≤2*t*(t-1)) (hc : 2*c=t*(t-1)) :
    q+1+3*t+K≤t*(q+1)+c := by
  have hgamma := dense_gamma_nonneg q t hq ht htq
  have hKQ : (3:ℚ)*(K:ℚ)≤2*(t:ℚ)*((t-1:ℕ):ℚ) := by exact_mod_cast hK
  have hcQ : (2:ℚ)*(c:ℚ)=(t:ℚ)*((t-1:ℕ):ℚ) := by exact_mod_cast hc
  rw [Nat.cast_sub (by omega : 1≤t)] at hKQ hcQ
  norm_num only [Nat.cast_one] at hKQ hcQ
  have hh : (q:ℚ)+1+3*(t:ℚ)+(K:ℚ)≤(t:ℚ)*((q:ℚ)+1)+(c:ℚ) := by
    nlinarith only [hgamma,hKQ,hcQ]
  exact_mod_cast hh

/-- Compatibility export for the former t ≥ 4 coefficient lemma. -/
theorem dense_large_coeff (q t K c : ℕ) (ht : 4≤t) (hq : t≤q)
    (hK : 3*K≤2*t*(t-1)) (hc : 2*c=t*(t-1)) :
    q+1+3*t+K≤t*(q+1)+c :=
  dense_coeff_ge_three q t K c (by omega) (by omega) hq hK hc

theorem dense_two_coeff (q j h : ℕ) (hq : 4≤q) (hs : h+j=q+1) :
    (q+7)*h≤(q+1)*(2*h+j+1) := by
  have hm := congrArg (fun n => q*n) hs
  have h5 := congrArg (fun n => 5*n) hs
  have hid : (q+1)*(2*h+j+1)+4*(q+1)=(q+7)*h+q*(q+1)+6*j := by
    nlinarith only [hm,h5]
  have hp := Nat.mul_le_mul_right (q+1) hq
  nlinarith only [hid,hp,Nat.zero_le j]

/-- V06 payment for all t ≥ 3, directly from the unified correction bound.
The binomial comparisons also apply to the top row j = q + 1. -/
theorem dense_payment_ge_three (q t P R K j : ℕ) (hq : 4≤q) (ht : 3≤t)
    (htq : t≤q) (hj : j≤q+1) (hP : P≤q+1+2*t) (hR : R≤t)
    (hK : 3*K≤2*t*(t-1)) :
    (j+1)*(q+1).choose (j+2)+P*q.choose j+R*(q+1).choose j+K*(q-1).choose j≤
      (j+1)*(q+t+1).choose (j+2) := by
  let B := (q+1).choose j
  let C := q.choose j
  let A := (q-1).choose j
  let h := q+1-j
  have hs : h+j=q+1 := Nat.sub_add_cancel hj
  have hsrow : h+(j+1)=q+2 := by omega
  have hAB : A≤B := Nat.choose_le_choose j (by omega)
  have hAC : A≤C := Nat.choose_le_choose j (by omega)
  have hCB : C≤B := Nat.choose_le_choose j (by omega)
  have ha : (j+1)*(q+1).choose (j+1)=h*B := by
    simpa only [Nat.mul_comm] using Nat.choose_succ_right_eq (q+1) j
  have hgap : (j+1)*(q+1).choose (j+2)+(t*h+t.choose 2*(j+1))*B≤
      (j+1)*(q+t+1).choose (j+2) := by
    calc
      (j+1)*(q+1).choose (j+2)+(t*h+t.choose 2*(j+1))*B=
          (j+1)*((q+1).choose (j+2)+t*(q+1).choose (j+1)+t.choose 2*B) := by
        have hh := congrArg (fun n => t*n) ha
        nlinarith only [hh]
      _≤(j+1)*((q+1)+t).choose (j+2) := Nat.mul_le_mul_left (j+1) (choose_add_two_terms (q+1) t j)
      _=(j+1)*(q+t+1).choose (j+2) := by rw [show q+1+t=q+t+1 by omega]
  change (j+1)*(q+1).choose (j+2)+P*C+R*B+K*A≤_
  have hc2 : 2*t.choose 2=t*(t-1) := by
    simpa only [Nat.choose_one_right,Nat.mul_comm] using Nat.choose_succ_right_eq t 1
  have hcoef := dense_coeff_ge_three q t K (t.choose 2) hq ht htq hK hc2
  have htC : t≤t.choose 2 := by
    have hm := Nat.mul_le_mul_left t (show 2≤t-1 by omega)
    nlinarith only [hm,hc2]
  have hmj := Nat.mul_le_mul_right j htC
  have hmt := congrArg (fun n => t*n) hs
  have hmin : t*(q+1)+t.choose 2≤t*h+t.choose 2*(j+1) := by nlinarith only [hmj,hmt]
  have hp := Nat.mul_le_mul hP hCB
  have hr := Nat.mul_le_mul_right B hR
  have hk := Nat.mul_le_mul_right B (hcoef.trans hmin)
  have hka := Nat.mul_le_mul_left K hAB
  nlinarith only [hp,hr,hk,hka,hgap]

/-- The separate t = 2 payment, using R = 0 and K ≤ 2. -/
theorem dense_payment_two (q P R K j : ℕ) (hq : 4≤q) (hj : j≤q+1)
    (hP : P≤q+5) (hR0 : R=0) (hK : K≤2) :
    (j+1)*(q+1).choose (j+2)+P*q.choose j+R*(q+1).choose j+K*(q-1).choose j≤
      (j+1)*(q+2+1).choose (j+2) := by
  let B := (q+1).choose j
  let C := q.choose j
  let A := (q-1).choose j
  let h := q+1-j
  have hs : h+j=q+1 := Nat.sub_add_cancel hj
  have hsrow : h+(j+1)=q+2 := by omega
  have hAB : A≤B := Nat.choose_le_choose j (by omega)
  have hAC : A≤C := Nat.choose_le_choose j (by omega)
  have hCB : C≤B := Nat.choose_le_choose j (by omega)
  have ha : (j+1)*(q+1).choose (j+1)=h*B := by
    simpa only [Nat.mul_comm] using Nat.choose_succ_right_eq (q+1) j
  have hgap : (j+1)*(q+1).choose (j+2)+(2*h+(2:ℕ).choose 2*(j+1))*B≤
      (j+1)*(q+2+1).choose (j+2) := by
    calc
      (j+1)*(q+1).choose (j+2)+(2*h+(2:ℕ).choose 2*(j+1))*B=
          (j+1)*((q+1).choose (j+2)+2*(q+1).choose (j+1)+(2:ℕ).choose 2*B) := by
        have hh := congrArg (fun n => 2*n) ha
        nlinarith only [hh]
      _≤(j+1)*((q+1)+2).choose (j+2) := Nat.mul_le_mul_left (j+1) (choose_add_two_terms (q+1) 2 j)
      _=(j+1)*(q+2+1).choose (j+2) := by rw [show q+1+2=q+2+1 by omega]
  change (j+1)*(q+1).choose (j+2)+P*C+R*B+K*A≤_
  have hP' : P≤q+5 := by omega
  have hrest : P*C+R*B+K*A≤(q+7)*C := by
    have hp := Nat.mul_le_mul_right C hP'
    have hk := Nat.mul_le_mul hK hAC
    rw [hR0] at *
    nlinarith only [hp,hk]
  have hc : (q+1)*C=h*B := by
    simpa only [Nat.mul_comm] using Nat.choose_mul_succ_eq q j
  have hcoef := dense_two_coeff q j h hq hs
  have hscaled : (q+1)*((q+7)*C)≤(q+1)*((2*h+j+1)*B) := by
    calc
      (q+1)*((q+7)*C)=(q+7)*h*B := by rw [show (q+1)*((q+7)*C)=(q+7)*((q+1)*C) by ring,hc]; ring
      _≤((q+1)*(2*h+j+1))*B := Nat.mul_le_mul_right B hcoef
      _=(q+1)*((2*h+j+1)*B) := by ring
  have hcost := Nat.le_of_mul_le_mul_left hscaled (by omega)
  norm_num only [Nat.choose_self] at hgap
  nlinarith only [hrest,hcost,hgap]

/-- The dense numerical payment, in the original positive rows through q+2.
All binomials are at genuine nonnegative indices j=i-1. -/
theorem dense_payment (q t P R K j : ℕ) (hq : 4≤q) (ht : 2≤t) (htq : t≤q) (hj : j≤q+1)
    (hP : P≤q+1+2*t) (hR : R≤t)
    (h2 : t=2 → R=0 ∧ K≤2) (h3 : t=3 → K≤4)
    (hlarge : 4≤t → 3*K≤2*t*(t-1)) :
    (j+1)*(q+1).choose (j+2)+P*q.choose j+R*(q+1).choose j+K*(q-1).choose j≤
      (j+1)*(q+t+1).choose (j+2) := by
  by_cases ht2 : t=2
  · obtain ⟨hR0,hK⟩ := h2 ht2
    subst t
    exact dense_payment_two q P R K j hq hj (by omega) hR0 hK
  · have ht3 : 3≤t := by omega
    have hK : 3*K≤2*t*(t-1) := by
      by_cases he : t=3
      · have hh := h3 he
        rw [he] at *
        omega
      · exact hlarge (by omega)
    exact dense_payment_ge_three q t P R K j hq ht3 htq hj hP hR hK
end NSP14.Width
