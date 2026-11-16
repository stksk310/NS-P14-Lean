module
public import NSP14.Endpoint.FirstHarmonic
public import NSP14.Endpoint.SocleBounds
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable def coreFirstBound : ℚ := (D.q : ℚ)+
  ∑ n∈Finset.range (D.u-1),((D.q-1 : ℕ) : ℚ)*(D.coreHilbert k (n+1):ℚ)/(n+2)

theorem QCore_first_floor : totalBetti k D.a (D.QCoreModule k) 1≤⌊D.coreFirstBound k⌋₊ :=
  Nat.le_floor (D.QCore_first_harmonic k)

/-- First actual full Betti row, with the real QC Hilbert function,
an actual natural floor, and the same-orientation Rhat. -/
theorem actual_first_row : totalBetti k D.Variables (D.fullG k) 1≤
    D.coreP k+⌊D.coreFirstBound k⌋₊+D.Rhat := by
  have h := D.actual_core_Rhat_bound k 1
  simp only [coreRhatRemainder,show (1:ℕ)≠0 by decide,ite_false,Nat.sub_self,
    Nat.choose_zero_right,mul_one] at h
  have hb := D.QCore_first_floor k
  omega

theorem completed_first_row : totalBetti k D.source.AtomExponent
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) 1≤
      D.coreP k+⌊D.coreFirstBound k⌋₊+D.Rhat := by
  rw [←D.source.completed_totalBetti k,←D.fullG_totalBetti k]
  exact D.actual_first_row k
end NSP14.Endpoint.Data
