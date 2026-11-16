module
public import NSP14.Endpoint.SocleBounds
public import NSP14.Endpoint.ArtinRank
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

/-- Additive form records feasibility of the subtraction in the row
package, derived from the actual signed-unit differential minor. -/
theorem actual_positive_rows_add (i : ℕ) (hi : 1 ≤ i) :
    totalBetti k D.Variables (D.fullG k) i+(D.q+1).choose (i+1)≤
      D.coreP k*(D.q+1).choose i+D.Rhat*(D.q+1).choose (i-1) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  have hf := D.actual_core_Rhat_bound k (j+1)
  have hA := D.QCore_positive_betti_add k (j+1) (by omega)
  simp only [coreRhatRemainder,show j+1≠0 by omega,ite_false,Nat.add_sub_cancel] at hf
  have hPascal := Nat.choose_succ_succ D.q j
  change (D.q+1).choose (j+1)=D.q.choose j+D.q.choose (j+1) at hPascal
  change totalBetti k D.Variables (D.fullG k) (j+1)+(D.q+1).choose (j+1+1)≤
    D.coreP k*(D.q+1).choose (j+1)+D.Rhat*(D.q+1).choose (j+1-1)
  rw [hPascal,Nat.add_sub_cancel]
  nlinarith only [hf,hA]

/-- Actual arbitrary-field positive rows, with the same resource data
and the same q internal versus q+2 full variables. -/
theorem actual_positive_rows (i : ℕ) (hi : 2 ≤ i) : totalBetti k D.Variables (D.fullG k) i≤
    D.coreP k*(D.q+1).choose i+D.Rhat*(D.q+1).choose (i-1)-(D.q+1).choose (i+1) :=
  Nat.le_sub_of_add_le (D.actual_positive_rows_add k i (by omega))

theorem completed_positive_rows (i : ℕ) (hi : 2 ≤ i) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i≤
        D.coreP k*(D.q+1).choose i+D.Rhat*(D.q+1).choose (i-1)-(D.q+1).choose (i+1) := by
  rw [←D.source.completed_totalBetti k,←D.fullG_totalBetti k]
  exact D.actual_positive_rows k i hi
end NSP14.Endpoint.Data
