module
public import NSP14.Endpoint.CoreHilbert
public import NSP14.Homological.FiniteDegreeSum
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem coreHilbert_card (n : ℕ) : D.coreHilbert k n=
    Nat.card {p : D.CoreMinimalIndex // D.coreDegree p.val=n} := by
  rw [coreHilbert,D.QCoreGrading_dimension]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun p => by change (D.coreDegree p.val : ℤ)=(n:ℤ) ↔ _;exact Nat.cast_inj)

theorem coreHilbert_sum : (∑ n∈Finset.range D.u,D.coreHilbert k n)=D.coreP k := by
  let d : D.CoreMinimalIndex → ℕ := fun p => D.coreDegree p.val
  have hdeg (p : D.CoreMinimalIndex) : d p≤D.u-1 := by
    change D.coreDegree p.val≤D.u-1
    have := D.coreMinimal_degree_lt p
    omega
  have h := finite_degree_sum d (D.u-1) hdeg (fun _ => (1:ℚ))
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,one_mul] at h
  rw [Nat.sub_add_cancel (show 1≤D.u from D.u_pos)] at h
  dsimp only [d] at h
  simp_rw [←D.coreHilbert_card k] at h
  rw [coreP,Module.finrank_eq_card_basis (D.QCoreBasis k)]
  exact_mod_cast h.symm
end NSP14.Endpoint.Data
