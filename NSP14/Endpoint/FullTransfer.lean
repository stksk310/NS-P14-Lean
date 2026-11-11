module
public import NSP14.Endpoint.Compensation
public import NSP14.Endpoint.Normalization
public import NSP14.Semigroup.AugmentationBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def coreRemainder (i : ℕ) : ℕ := if i=0 then 0 else
  D.coreP k*D.q.choose (i-1)+D.actualR k*(D.q+1).choose (i-1)

theorem compensation_merge (i : ℕ) :
    (if i=0 then 0 else (D.coreP k-D.actualP k)*D.q.choose (i-1))+D.endpointRemainder k i=
      D.coreRemainder k i := by
  have hP : D.coreP k-D.actualP k+D.actualP k=D.coreP k := Nat.sub_add_cancel (D.actualP_le_coreP k)
  cases i with
  | zero => simp [endpointRemainder,coreRemainder]
  | succ i =>
    cases i with
    | zero =>
      simp only [Nat.add_sub_cancel,show (0+1:ℕ)≠0 by decide,ite_false,endpointRemainder,
        coreRemainder,show (1:ℕ)≤1 by decide,ite_true,show ¬(2:ℕ)≤1 by decide,
        Nat.choose_zero_right,mul_one,add_zero]
      omega
    | succ i =>
      have hPascal := Nat.choose_succ_succ D.q i
      simp only [endpointRemainder,coreRemainder,show i+1+1≠0 by omega,ite_false,
        show 1 ≤ i+1+1 by omega,show 2 ≤ i+1+1 by omega,ite_true,
        show i+1+1-1=i+1 by omega,show i+1+1-2=i by omega]
      rw [hPascal]
      nlinarith only [congrArg (fun z => z*D.q.choose (i+1)) hP]

/-- Kernel-compensated all-row bound, on the actual full minimal
presentation. The zero row is guarded explicitly. -/
theorem actual_core_endpoint_bound (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤
    totalBetti k D.a (D.QCoreModule k) i+D.coreRemainder k i := by
  have hn := D.actual_native_endpoint_bound k i
  have hk := D.actual_kernel_compensation k i
  have h := hn.trans (Nat.add_le_add_right hk (D.endpointRemainder k i))
  rw [add_assoc,D.compensation_merge] at h
  exact h

/-- The same bound is exported to the actual completed semigroup
ring tangent cone over the original coefficient field. -/
theorem completed_core_endpoint_bound (i : ℕ) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i≤
        totalBetti k D.a (D.QCoreModule k) i+D.coreRemainder k i := by
  rw [←D.source.completed_totalBetti k,←D.fullG_totalBetti k]
  exact D.actual_core_endpoint_bound k i

theorem actual_endpoint_top : totalBetti k D.Variables (D.fullG k) (D.q+2)≤D.actualR k := by
  have h := D.actual_core_endpoint_bound k (D.q+2)
  have hb : totalBetti k D.a (D.QCoreModule k) (D.q+2)=0 :=
    totalBetti_eq_zero_of_gt k D.a _ _ (by simp only [Fintype.card_coe];unfold q;omega)
  rw [hb,coreRemainder] at h
  simp only [show D.q+2≠0 by omega,ite_false,show D.q+2-1=D.q+1 by omega,
    Nat.choose_eq_zero_of_lt (show D.q<D.q+1 by omega),mul_zero,Nat.choose_self,mul_one,zero_add] at h
  exact h

theorem actual_endpoint_above (i : ℕ) (hi : D.q+2 < i) : totalBetti k D.Variables (D.fullG k) i=0 :=
  totalBetti_eq_zero_of_gt k D.Variables _ i (by rw [D.variables_card];exact hi)

theorem actual_endpoint_zero : totalBetti k D.Variables (D.fullG k) 0=1 := by
  rw [D.fullG_totalBetti]
  exact D.source.actualG_totalBetti_zero k
end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2)
    (k : Type) [Field k]

/-- Narrow normalization returns the same original actual completed
cone and the original field, not an auxiliary profile. -/
theorem narrow_endpoint_core_bound (i : ℕ) :
    NSP14.Homological.totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
    NSP14.Homological.totalBetti k (S.endpointData he hw).a ((S.endpointData he hw).QCoreModule k) i+
      (S.endpointData he hw).coreRemainder k i := by
  rw [←S.completed_totalBetti k,←S.endpointData_totalBetti he hw k,←(S.endpointData he hw).fullG_totalBetti k]
  exact (S.endpointData he hw).actual_core_endpoint_bound k i
end NSP14.NumericalSemigroup
