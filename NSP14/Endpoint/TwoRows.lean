module
public import NSP14.Endpoint.TwoInternal
public import NSP14.Endpoint.SocleBounds
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem actual_two_row_one (hq : D.q=2) : totalBetti k D.Variables (D.fullG k) 1≤
    D.coreP k+D.internalSigma k hq+1+D.actualR k := by
  have h := D.actual_core_endpoint_bound k 1
  rw [D.QCore_two_betti_one k hq] at h
  norm_num [coreRemainder,hq] at h
  omega

theorem actual_two_row_two (hq : D.q=2) : totalBetti k D.Variables (D.fullG k) 2≤
    2*D.coreP k+D.internalSigma k hq+3*D.actualR k := by
  have h := D.actual_core_endpoint_bound k 2
  rw [D.QCore_two_betti_two k hq] at h
  norm_num [coreRemainder,hq] at h
  omega

theorem actual_two_row_three (hq : D.q=2) : totalBetti k D.Variables (D.fullG k) 3≤D.coreP k+3*D.actualR k := by
  have h := D.actual_core_endpoint_bound k 3
  rw [D.QCore_two_betti_above k hq 3 (by omega)] at h
  norm_num [coreRemainder,hq] at h
  omega

theorem actual_two_row_four (hq : D.q=2) : totalBetti k D.Variables (D.fullG k) 4≤D.actualR k := by
  have h := D.actual_endpoint_top k
  simpa only [hq] using h

theorem actual_two_row_one_Rhat (hq : D.q=2) : totalBetti k D.Variables (D.fullG k) 1≤
    D.coreP k+D.internalSigma k hq+1+D.Rhat := by
  have h := D.actual_two_row_one k hq
  have hr := D.actualR_le_Rhat k
  omega

theorem actual_two_row_two_Rhat (hq : D.q=2) : totalBetti k D.Variables (D.fullG k) 2≤
    2*D.coreP k+D.internalSigma k hq+3*D.Rhat := by
  have h := D.actual_two_row_two k hq
  have hr := D.actualR_le_Rhat k
  omega

theorem actual_two_row_three_Rhat (hq : D.q=2) : totalBetti k D.Variables (D.fullG k) 3≤D.coreP k+3*D.Rhat := by
  have h := D.actual_two_row_three k hq
  have hr := D.actualR_le_Rhat k
  omega

theorem actual_two_row_four_Rhat (hq : D.q=2) : totalBetti k D.Variables (D.fullG k) 4≤D.Rhat := by
  have h := D.actual_endpoint_top_Rhat k
  simpa only [hq] using h

noncomputable def twoRowBound (hq : D.q=2) (i : ℕ) : ℕ :=
  if i=0 then 1 else if i=1 then D.coreP k+D.internalSigma k hq+1+D.Rhat else
    if i=2 then 2*D.coreP k+D.internalSigma k hq+3*D.Rhat else
      if i=3 then D.coreP k+3*D.Rhat else if i=4 then D.Rhat else 0

theorem actual_two_all_rows (hq : D.q=2) (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤D.twoRowBound k hq i := by
  by_cases h0 : i=0
  · subst i
    rw [D.actual_endpoint_zero]
    simp [twoRowBound]
  by_cases h1 : i=1
  · subst i
    simpa [twoRowBound] using D.actual_two_row_one_Rhat k hq
  by_cases h2 : i=2
  · subst i
    simpa [twoRowBound] using D.actual_two_row_two_Rhat k hq
  by_cases h3 : i=3
  · subst i
    simpa [twoRowBound] using D.actual_two_row_three_Rhat k hq
  by_cases h4 : i=4
  · subst i
    simpa [twoRowBound] using D.actual_two_row_four_Rhat k hq
  rw [D.actual_endpoint_above k i (by rw [hq];omega)]
  exact Nat.zero_le _

theorem completed_two_all_rows (hq : D.q=2) (i : ℕ) : totalBetti k D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i≤D.twoRowBound k hq i := by
  rw [←D.source.completed_totalBetti k,←D.fullG_totalBetti k]
  exact D.actual_two_all_rows k hq i
end NSP14.Endpoint.Data
