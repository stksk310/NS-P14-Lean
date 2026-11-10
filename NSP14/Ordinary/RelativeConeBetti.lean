module
public import NSP14.Ordinary.RelativeSomeKoszul
public import NSP14.Homological.CoefficientConeBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex NSP14.Homological
namespace NSP14.Ordinary.ActualWitness
variable {k : Type} [Field k] (W : ActualWitness k)
local notation "L" => ScalarField (k:=k)

noncomputable def relativeSomeCone : ChainComplex (ModuleCat L) ℕ :=
  coefficientActionCone L (Option (Fin W.source.actualCutRank)) W.someVariables
    (W.algebraRestriction.obj (W.source.algebraG L))
    (W.algebraRestriction.map (W.source.algebraXProjection L ≫ W.source.algebraImageInclusion L))

/-- Actual ordinary R Tor, with the separately proved R-finite G input.
No P-finite or k-finite assertion about G enters this identification. -/
theorem relativeSomeCone_Euler (j : ℕ) :
    letI := W.relativeG_finite
    complexEuler L W.relativeSomeCone j=
      bettiEuler L (Option (Fin W.source.actualCutRank)) W.relativeG j := by
  let := W.relativeG_finite
  let : Module.Finite W.RelativeRing (W.algebraRestriction.obj (W.source.algebraG L)) :=
    Module.Finite.equiv W.algebraRestrictionGIso.symm.toLinearEquiv
  calc
    _ = bettiEuler L (Option (Fin W.source.actualCutRank))
        (W.algebraRestriction.obj (W.source.algebraG L)) j := by
      unfold relativeSomeCone
      exact coefficientActionCone_Euler L (Option (Fin W.source.actualCutRank)) none W.someVariables
        W.mem_relativeVariableOrder W.relativeVariableOrder_nodup
        (W.algebraRestriction.obj (W.source.algebraG L))
        (W.algebraRestriction.map (W.source.algebraXProjection L ≫ W.source.algebraImageInclusion L))
        W.relative_algebraX_scalar j
    _ = _ := congrArg (fun b : ℕ → ℕ => partialEuler b j)
      (funext (totalBetti_iso L (Option (Fin W.source.actualCutRank)) W.algebraRestrictionGIso))
end NSP14.Ordinary.ActualWitness
