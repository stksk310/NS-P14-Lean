module
public import NSP14
@[expose] public section
open NSP14 NSP14.Homological
namespace CarrierTransportAcceptance
variable (S T : NumericalSemigroup) (h : S.carrier=T.carrier) (k : Type) [Field k]
include h

theorem graded_algebra : Nonempty (S.TangentAlgebra k ≃ₐ[k] T.TangentAlgebra k) := by
  exact ⟨S.carrierTangentEquiv T h k⟩

theorem actual_Betti (i : ℕ) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i=
      totalBetti k T.AtomExponent (ModuleCat.of (T.FullPolynomialRing k) (T.TangentAlgebra k)) i :=
  S.carrier_totalBetti T h k i
end CarrierTransportAcceptance
