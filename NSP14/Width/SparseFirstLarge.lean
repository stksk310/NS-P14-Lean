module
public import NSP14.Width.FirstResources
public import NSP14.Target.IntervalAPBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological
namespace NSP14.Width

/-- The exact universal first-row difference, with z the excess over the sparse threshold. -/
theorem sparse_first_large_payment (e u : ℕ) (he : 10≤e) (hu : 2*e-2≤u) :
    ((e:ℚ)+3)/3*((u:ℚ)^2/((e:ℚ)-1))-(u:ℚ)+(e:ℚ)*((e:ℚ)-1)/6≤
      (u.choose 2:ℚ)+1 := by
  have heQ : (10:ℚ)≤e := by exact_mod_cast he
  have huQ : 2*(e:ℚ)-2≤u := by
    have h : 2*(e:ℚ)≤(u:ℚ)+2 := by exact_mod_cast (show 2*e≤u+2 by omega)
    linarith only [h]
  let z : ℚ := (u:ℚ)-(2*(e:ℚ)-2)
  have hz : 0≤z := by dsimp [z];linarith
  have hd : (e:ℚ)-1≠0 := by linarith
  have hid : (u:ℚ)*((u:ℚ)-1)/2+1-
      (((e:ℚ)+3)/3*((u:ℚ)^2/((e:ℚ)-1))-(u:ℚ)+(e:ℚ)*((e:ℚ)-1)/6)=
      ((e:ℚ)-1)*((e:ℚ)-10)/2+1+(4*(e:ℚ)-33)*z/6+
        ((e:ℚ)-9)*z^2/(6*((e:ℚ)-1)) := by
    dsimp [z]
    field_simp
    ring
  have h1 : 0≤((e:ℚ)-1)*((e:ℚ)-10)/2 := by
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · norm_num
  have h2 : 0≤(4*(e:ℚ)-33)*z/6 := by
    exact div_nonneg (mul_nonneg (by linarith) hz) (by norm_num)
  have h3 : 0≤((e:ℚ)-9)*z^2/(6*((e:ℚ)-1)) := by
    exact div_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_nonneg (by norm_num) (by linarith))
  rw [choose_two_rat]
  linarith only [hid,h1,h2,h3]
end NSP14.Width
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

/-- The actual source's first row on the infinite e>=10 sparse range. -/
theorem actual_first_sparse_large (he : 10≤D.q+2) (hu : 2*(D.q+2)-2≤D.u) :
    totalBetti k D.Variables (D.fullG k) 1≤D.u.choose 2+1 := by
  have h := D.actual_first_quadratic k
  have hp := NSP14.Width.sparse_first_large_payment (D.q+2) D.u he hu
  push_cast at hp
  have heq : ((D.q:ℚ)+2-1)=(D.q:ℚ)+1 := by ring
  rw [heq] at hp
  have hbound : (totalBetti k D.Variables (D.fullG k) 1:ℚ)≤(D.u.choose 2:ℚ)+1 := by
    nlinarith only [h,hp]
  exact_mod_cast hbound

/-- Export to the same completed source; no Cohen--Macaulay hypothesis. -/
theorem completed_first_sparse_large (he : 10≤D.q+2) (hu : 2*(D.q+2)-2≤D.u) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) 1≤
        D.u.choose 2+1 := by
  rw [←D.source.completed_totalBetti k,←D.fullG_totalBetti k]
  exact D.actual_first_sparse_large k he hu
end NSP14.Endpoint.Data

namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

set_option synthInstance.maxHeartbeats 200000 in
/-- An infinite sparse range, connected to both actual completed tangent cones. -/
theorem narrow_sparse_large_first_comparison (he : 10≤S.embeddingDimension)
    (hw : S.width≤S.multiplicity-2)
    (hu : 2*S.embeddingDimension-2≤S.normalizedWidth) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) 1≤
    totalBetti k (S.intervalCompletion (le_trans (by decide : 2≤10) he)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (le_trans (by decide : 2≤10) he)).FullPolynomialRing k)
        ((S.intervalCompletion (le_trans (by decide : 2≤10) he)).FormalTangentAlgebra k)) 1 := by
  let D := S.endpointData (by omega) hw
  have hD : D.q+2=S.embeddingDimension := S.endpointData_embedding (by omega) hw
  have heD : 10≤D.q+2 := by omega
  have huD : 2*(D.q+2)-2≤D.u := by
    change 2*(D.q+2)-2≤S.normalizedWidth
    omega
  have hb : totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) 1≤D.u.choose 2+1 := by
    rw [←S.completed_totalBetti k,←S.endpointData_totalBetti (by omega) hw k,←D.fullG_totalBetti k]
    exact D.actual_first_sparse_large k heD huD
  have hwidth : D.u≤S.width := by
    change S.normalizedWidth≤S.width
    have hf := S.width_factor
    have hd := S.offsetGcd_pos (by omega : 2≤S.embeddingDimension)
    nlinarith only [hf,hd]
  have hm : min S.width (S.multiplicity-1)=S.width := min_eq_left (by omega)
  have ht := S.interval_completed_betti_lower k (by omega) 1 (by omega)
  rw [hm] at ht
  have hp := S.width_pos (by omega : 2≤S.embeddingDimension)
  simp only [NSP14.Target.apLowerProfile,Nat.one_mul,Nat.reduceAdd,Nat.sub_self,
    Nat.choose_zero_right,Nat.choose_one_right,min_eq_left hp] at ht
  exact hb.trans ((Nat.add_le_add_right (Nat.choose_le_choose 2 hwidth) 1).trans ht)
end NSP14.NumericalSemigroup
