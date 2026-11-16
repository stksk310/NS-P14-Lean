module
public import NSP14.Homological.GradedKoszulBasis
@[expose] public section
namespace NSP14.Tests.GradedKoszulBasis
theorem actual_basis_coordinates (k σ J : Type) [Field k]
    (M : ModuleCat (Homological.VariableRing k σ)) (G : Homological.GradedPolynomialModule k σ M)
    (b : Module.Basis J k (Homological.coefficientModule k σ M)) (deg : J → ℤ)
    (hb : ∀ a,b a ∈ G.degreeSpace (deg a)) (xs : List σ) (t : ℤ) (i : ℕ) :
    Nonempty (Module.Basis {a : Homological.KoszulSlot xs.length i × J //deg a.2=t-(i:ℤ)} k
      (Homological.gradedKoszulSpace k σ M G xs t i)) :=
  ⟨Homological.gradedKoszulSpaceBasis k σ M G b deg hb xs t i⟩
end NSP14.Tests.GradedKoszulBasis
