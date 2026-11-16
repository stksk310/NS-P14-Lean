module
public import NSP14.Endpoint.SocleInjection
public import NSP14.Endpoint.FullTransfer
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable instance competitorSocleFinite (s : Fin D.u) :
    Module.Finite k (NSP14.Endpoint.coordinateSocle k (D.competitorFiber s)) := by
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  exact NSP14.Endpoint.coordinateSocle_finite k (D.competitorFiber s) (D.competitorFiber_upward s) c hc

theorem competitorSocle_dimension (s : Fin D.u) :
    Module.finrank k (NSP14.Endpoint.coordinateSocle k (D.competitorFiber s))≤D.competitorZ s := by
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  exact NSP14.Endpoint.coordinateSocle_finrank_bound k (D.competitorFiber s) (D.competitorFiber_upward s) c hc

/-- The real endpoint socle injects into the real T_s quotient socles;
finite-dimensionality is required only for those socles. -/
theorem actualR_le_sum_z : D.actualR k≤∑ s : Fin D.u,D.competitorZ s := by
  let : ∀ s : Fin D.u,Module.Finite k (NSP14.Endpoint.coordinateSocle k (D.competitorFiber s)) :=
    fun s => D.competitorSocleFinite k s
  let : ∀ s : Fin D.u,Module.Free k (NSP14.Endpoint.coordinateSocle k (D.competitorFiber s)) :=
    fun s => Module.Free.of_divisionRing k _
  have h := LinearMap.finrank_le_finrank_of_injective (D.actualSocleProductMap_injective k)
  rw [Module.finrank_pi_fintype] at h
  rw [D.actualR_socle_dimension]
  exact h.trans (Finset.sum_le_sum (fun s _ => D.competitorSocle_dimension k s))

theorem actualR_le_volume : D.actualR k≤D.wordVolume-D.u :=
  (D.actualR_le_sum_z k).trans D.competitorZ_sum_bound

theorem actualR_le_height : D.actualR k≤D.u*(D.coreHeight-2) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => D.competitorZ_height s)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  exact (D.actualR_le_sum_z k).trans hs

/-- Same-orientation resource: no reflected core is used. Nat subtraction
is max(Hx-2,0); W>=u is proved independently below. -/
noncomputable def Rhat : ℕ := min (D.wordVolume-D.u) (D.u*(D.coreHeight-2))

theorem wordVolume_ge_u : D.u≤D.wordVolume := by
  rw [D.wordVolume_coordinates]
  omega

theorem actualR_le_Rhat : D.actualR k≤D.Rhat :=
  le_min (D.actualR_le_volume k) (D.actualR_le_height k)

noncomputable def coreRhatRemainder (i : ℕ) : ℕ := if i=0 then 0 else
  D.coreP k*D.q.choose (i-1)+D.Rhat*(D.q+1).choose (i-1)

theorem coreRemainder_le_Rhat (i : ℕ) : D.coreRemainder k i≤D.coreRhatRemainder k i := by
  unfold coreRemainder coreRhatRemainder
  split_ifs
  · rfl
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (D.actualR_le_Rhat k)) _

theorem actual_core_Rhat_bound (i : ℕ) :
    NSP14.Homological.totalBetti k D.Variables (D.fullG k) i≤
      NSP14.Homological.totalBetti k D.a (D.QCoreModule k) i+D.coreRhatRemainder k i :=
  (D.actual_core_endpoint_bound k i).trans (Nat.add_le_add_left (D.coreRemainder_le_Rhat k i) _)

theorem completed_core_Rhat_bound (i : ℕ) :
    NSP14.Homological.totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i≤
        NSP14.Homological.totalBetti k D.a (D.QCoreModule k) i+D.coreRhatRemainder k i :=
  (D.completed_core_endpoint_bound k i).trans (Nat.add_le_add_left (D.coreRemainder_le_Rhat k i) _)

theorem actual_endpoint_top_Rhat : NSP14.Homological.totalBetti k D.Variables (D.fullG k) (D.q+2)≤D.Rhat :=
  (D.actual_endpoint_top k).trans (D.actualR_le_Rhat k)
end NSP14.Endpoint.Data
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (he : 4≤S.embeddingDimension) (hw : S.width≤S.multiplicity-2)
    (k : Type) [Field k]

theorem narrow_endpoint_core_Rhat_bound (i : ℕ) :
    NSP14.Homological.totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i≤
    NSP14.Homological.totalBetti k (S.endpointData he hw).a ((S.endpointData he hw).QCoreModule k) i+
      (S.endpointData he hw).coreRhatRemainder k i := by
  rw [←S.completed_totalBetti k,←S.endpointData_totalBetti he hw k,←(S.endpointData he hw).fullG_totalBetti k]
  exact (S.endpointData he hw).actual_core_Rhat_bound k i
end NSP14.NumericalSemigroup
