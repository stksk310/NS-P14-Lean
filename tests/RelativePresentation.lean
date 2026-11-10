module
public import NSP14
@[expose] public section
open NSP14 NSP14.NumericalSemigroup NSP14.Ordinary
namespace RelativePresentationAcceptance
variable {k : Type} [Field k] (W : ActualWitness k)
theorem relative_variable_count :
    Fintype.card (Option (Fin W.source.actualCutRank))=W.source.actualCutRank+1 := by simp

theorem relative_x : W.relativeToG (MvPolynomial.X none)=W.source.xElement (NSP14.Homological.InfiniteScalarField k) :=
  W.relativeToG_X_none
theorem actual_relative_embedding : Function.Injective W.relativeToFull := W.relativeToFull_injective
end RelativePresentationAcceptance
namespace RelativePresentationAcceptance
open NSP14 NSP14.Ordinary
variable {k : Type} [Field k] (W : ActualWitness k)
theorem finite_actual_R_source : Module.Finite W.RelativeRing W.relativeG := W.relativeG_finite
end RelativePresentationAcceptance
