module
public import NSP14.Width.FiveHoleComparison
public import NSP14.Width.AntipodalComparison
public import NSP14.Width.EdgeAP
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]
/-- Five actual minimal generators, every normalized width and every
Betti row, on the original completed source and literal interval target. -/
theorem narrow_five_comparison (he : S.embeddingDimension=5)
    (hw : S.width ≤ S.multiplicity-2) (i : ℕ) :
    totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i ≤ 
    totalBetti k (S.intervalCompletion (by omega)).AtomExponent
      (ModuleCat.of ((S.intervalCompletion (by omega)).FullPolynomialRing k)
        ((S.intervalCompletion (by omega)).FormalTangentAlgebra k)) i := by
  let D := S.endpointData (by omega) hw
  have hD := S.endpointData_embedding (by omega) hw
  have hq : D.q=3 := by change D.q+2=S.embeddingDimension at hD; omega
  have hu4 : 4 ≤ S.normalizedWidth := by
    have h := D.q_add_one_le_u
    change D.q+1 ≤ S.normalizedWidth at h
    omega
  by_cases hu : S.normalizedWidth=4
  · exact S.narrow_fullAP_comparison k (by omega) hw (by change D.u=D.q+1; have huD : D.u=4 := hu; omega) i
  by_cases hu5 : S.normalizedWidth=5
  · exact S.narrow_five_hole_comparison k he hw hu5 i
  by_cases hu7 : S.normalizedWidth ≤ 7
  · exact S.narrow_five_small_comparison k he hw (by omega) i
  · exact S.narrow_five_large_comparison k he hw (by omega) i
end NSP14.NumericalSemigroup
