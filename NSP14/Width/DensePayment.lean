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

theorem dense_large_coeff (q t K c : ℕ) (ht : 4≤t) (hq : t≤q)
    (hK : 3*K≤2*t*(t-1)) (hc : 2*c=t*(t-1)) :
    q+1+3*t+K≤t*(q+1)+c := by
  obtain ⟨z,rfl⟩ := Nat.exists_eq_add_of_le ht
  obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le hq
  rw [show 4+z-1=3+z by omega] at hK hc
  nlinarith only [hK,hc,Nat.zero_le (z*z),Nat.zero_le (z*v),Nat.zero_le z,Nat.zero_le v]

theorem dense_two_coeff (q j h : ℕ) (hq : 4≤q) (hs : h+j=q+1) :
    (q+7)*h≤(q+1)*(2*h+j+1) := by
  have hm := congrArg (fun n => q*n) hs
  have h5 := congrArg (fun n => 5*n) hs
  have hid : (q+1)*(2*h+j+1)+4*(q+1)=(q+7)*h+q*(q+1)+6*j := by
    nlinarith only [hm,h5]
  have hp := Nat.mul_le_mul_right (q+1) hq
  nlinarith only [hid,hp,Nat.zero_le j]

/-- The dense numerical payment, in the original positive rows through q+2.
All binomials are at genuine nonnegative indices j=i-1. -/
theorem dense_payment (q t P R K j : ℕ) (hq : 4≤q) (ht : 2≤t) (htq : t≤q) (hj : j≤q+1)
    (hP : P≤q+1+2*t) (hR : R≤t)
    (h2 : t=2 → R=0 ∧ K≤2) (h3 : t=3 → K≤4)
    (hlarge : 4≤t → 3*K≤2*t*(t-1)) :
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
  by_cases ht2 : t=2
  · obtain ⟨hR0,hK⟩ := h2 ht2
    subst t
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
  · by_cases ht3 : t=3
    · have hK := h3 ht3
      subst t
      have hp := Nat.mul_le_mul hP hCB
      have hr := Nat.mul_le_mul_right B hR
      have hk := Nat.mul_le_mul hK hAB
      have hcoef : q+1+6+3+4≤3*(q+2) := by omega
      have hm := Nat.mul_le_mul_right B hcoef
      have he : (3*h+3*(j+1))*B=3*(q+2)*B := by rw [← Nat.mul_add,hsrow]
      norm_num at hgap
      nlinarith only [hp,hr,hk,hm,hgap,he]
    · have ht4 : 4≤t := by omega
      have hK := hlarge ht4
      have hc2 : 2*t.choose 2=t*(t-1) := by
        simpa only [Nat.choose_one_right,Nat.mul_comm] using Nat.choose_succ_right_eq t 1
      have hcoef := dense_large_coeff q t K (t.choose 2) ht4 htq hK hc2
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
end NSP14.Width

