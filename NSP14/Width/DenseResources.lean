module
public import NSP14.Width.DenseHeight
@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]
/-- All dense resources refer to the original endpoint core and original
socle, over any coefficient field; q=3 is included. -/
theorem dense_resources (t : ℕ) (hu : D.u=D.q+1+t) (ht : t≤D.q) :
    D.wordVolume=D.q+1+2*t ∧ D.coreP k≤D.q+1+2*t ∧ D.actualR k≤t ∧
    (t≤2 → D.actualR k=0) ∧ D.coreHeight≤t := by
  have hH : D.coreHeight≤t := by
    have h := D.coreHeight_le_missing
    omega
  refine ⟨D.dense_wordVolume t hu ht,D.dense_coreP k t hu ht,
    D.dense_actualR k t hu ht,?_,hH⟩
  intro ht2
  have h := D.actualR_le_height k
  have hz : D.coreHeight-2=0 := by omega
  rw [hz,Nat.mul_zero] at h
  exact Nat.eq_zero_of_le_zero h
end NSP14.Endpoint.Data
