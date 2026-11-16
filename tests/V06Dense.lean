module
public import NSP14.Width.DenseComparison
public import tests.WidthDenseResources
@[expose] public section
namespace NSP14.Tests.V06Dense
open NSP14.Homological

/-- The unified coefficient is allowed to vanish at the smallest dense boundary. -/
theorem gamma_q4_t3_zero :
    (5*(3:ℚ)^2-17*(3:ℚ)-6)/6+((3:ℚ)-1)*((4:ℚ)-(3:ℚ))=0 := by
  norm_num

/-- The first-row payment can be equality, so no strict inequality is required. -/
theorem q4_t3_j0_eq :
    (0+1)*(5:ℕ).choose (0+2)+11*(4:ℕ).choose 0+
      3*(5:ℕ).choose 0+4*(3:ℕ).choose 0=
      (0+1)*(8:ℕ).choose (0+2) := by
  decide

/-- All positive rows, including j = q + 1, use the new t ≥ 3 payment. -/
theorem q4_t3_all_rows (j : ℕ) (hj : j≤5) :
    (j+1)*(5:ℕ).choose (j+2)+11*(4:ℕ).choose j+
      3*(5:ℕ).choose j+4*(3:ℕ).choose j≤(j+1)*(8:ℕ).choose (j+2) :=
  Width.dense_payment_ge_three 4 3 11 3 4 j (by decide) (by decide) (by decide)
    hj (by decide) (by decide) (by decide)

/-- Top-row binomials are not cancelled or divided out. -/
theorem top_row (q t P R K : ℕ) (hq : 4≤q) (ht : 3≤t) (htq : t≤q)
    (hP : P≤q+1+2*t) (hR : R≤t) (hK : 3*K≤2*t*(t-1)) :
    (q+1+1)*(q+1).choose (q+1+2)+P*q.choose (q+1)+R*(q+1).choose (q+1)+
      K*(q-1).choose (q+1)≤(q+1+1)*(q+t+1).choose (q+1+2) :=
  Width.dense_payment_ge_three q t P R K (q+1) hq ht htq (by omega) hP hR hK

/-- The actual consumer retains the top source row, over any field. -/
theorem q4_t3_actual_top (k : Type) [Field k] :
    totalBetti k DenseResources.q4_t3.Variables (DenseResources.q4_t3.fullG k) 6≤
      6*DenseResources.q4_t3.u.choose 7 :=
  DenseResources.q4_t3.actual_dense_firstterm k 3 (by decide) (by decide) (by decide)
    (by decide) 6 (by decide)

/-- The single-quotient resource helper does not narrow the old quantified range. -/
theorem resources_full_range (D : Endpoint.Data) (k : Type) [Field k] (t : ℕ)
    (hu : D.u=D.q+1+t) (ht : t≤D.q) (hq : 4≤D.q) :
    ∃ K : ℕ,(∀ i : ℕ,1 ≤ i → totalBetti k D.a (D.QCoreModule k) i≤
      i*(D.q+1).choose (i+1)+K*(D.q-1).choose (i-1)) ∧
      (t=2 → K≤2) ∧ (3≤t → 3*K≤2*t*(t-1)) :=
  D.dense_core_lex_bound_two_branch k t hu ht hq

end NSP14.Tests.V06Dense
