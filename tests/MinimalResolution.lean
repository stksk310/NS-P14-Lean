module

public import NSP14

@[expose] public section
open NSP14.Homological
namespace MinimalResolutionAcceptance
variable (k σ : Type) [Field k] [Fintype σ]
variable (M : ModuleCat (VariableRing k σ)) [Module.Finite (VariableRing k σ) M]
/-- Both a genuine projective resolution and its rank comparison are available from actual covers. -/
noncomputable def actual_resolution (T : MinimalFreeTower k σ M) : CategoryTheory.ProjectiveResolution M :=
  T.toProjectiveResolution

theorem resolution_rank (T : MinimalFreeTower k σ M) (i : ℕ) : totalBetti k σ M i=T.rank i :=
  minimalResolutionBetti k σ T i
end MinimalResolutionAcceptance
