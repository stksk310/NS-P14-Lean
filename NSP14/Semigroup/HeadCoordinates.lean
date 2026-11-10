module

public import NSP14.Semigroup.ShiftCoordinates
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

def TerminalExponent := {x : S.carrier // S.Terminal x.val}
def HeadExponent := {y : S.carrier // S.XHead y.val}

noncomputable def coordinateKernelEquiv : (S.coordinateShift k).ker ≃ₗ[k]
    (S.TerminalExponent →₀ k) :=
  (LinearEquiv.ofEq _ _ (S.coordinateShift_ker k)).trans
    (Finsupp.supportedEquivFinsupp {x : S.carrier | S.Terminal x.val})

noncomputable def headProjection : (S.carrier →₀ k) →ₗ[k] (S.HeadExponent →₀ k) :=
  Finsupp.lsubtypeDomain {y : S.carrier | S.XHead y.val}

theorem headProjection_surjective : Function.Surjective (S.headProjection k) := by
  classical
  intro g
  exact ⟨g.extendDomain, Finsupp.subtypeDomain_extendDomain g⟩

theorem headProjection_ker : (S.headProjection k).ker = (S.coordinateShift k).range := by
  classical
  rw [S.coordinateShift_range]
  ext f
  change Finsupp.subtypeDomain _ f = 0 ↔ _
  rw [Finsupp.subtypeDomain_eq_zero_iff', Finsupp.mem_supported']
  simp only [Set.mem_ofPred_eq, not_not]

/-- Coefficient-level cokernel, with the actual live-shift range as denominator. -/
noncomputable def coordinateHeadQuotientEquiv :
    ((S.carrier →₀ k) ⧸ (S.coordinateShift k).range) ≃ₗ[k] (S.HeadExponent →₀ k) :=
  (Submodule.quotEquivOfEq _ _ (S.headProjection_ker k).symm).trans
    ((S.headProjection k).quotKerEquivOfSurjective (S.headProjection_surjective k))

end NSP14.NumericalSemigroup
