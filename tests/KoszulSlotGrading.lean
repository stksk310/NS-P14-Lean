module
public import NSP14.Homological.KoszulSlotGrading
@[expose] public section
namespace NSP14.Tests.KoszulSlotGrading
theorem actual_basis_homogeneous (k σ J : Type) [Field k]
    (M : ModuleCat (Homological.VariableRing k σ)) (G : Homological.GradedPolynomialModule k σ M)
    (b : Module.Basis J k (Homological.coefficientModule k σ M)) (deg : J → ℤ)
    (hb : ∀ a,b a ∈ G.degreeSpace (deg a)) (xs : List σ) (i : ℕ)
    (a : Homological.KoszulSlot xs.length i × J) :
    Homological.koszulSlotBasis k σ M b xs i a ∈
      (Homological.koszulChainGrading k σ M G xs i).degreeSpace (deg a.2) :=
  Homological.koszulSlotBasis_homogeneous k σ M G b deg hb xs i a
end NSP14.Tests.KoszulSlotGrading
