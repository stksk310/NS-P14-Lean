module
public import NSP14
@[expose] public section
open CategoryTheory
namespace GradedBasisAcceptance
open NSP14.Homological
variable (k σ J : Type) [Field k] (M : ModuleCat (VariableRing k σ))
  (G : GradedPolynomialModule k σ M) (B : Module.Basis J k (coefficientModule k σ M))
  (deg : J → ℤ) (hB : ∀ i,B i ∈ G.degreeSpace (deg i))
include hB in
theorem actual_homogeneous_coordinates (q : ℤ) (a : coefficientModule k σ M)
    (ha : a ∈ G.degreeSpace q) (i : J) (hi : deg i ≠ q) : B.repr a i=0 :=
  gradedBasis_repr_zero k σ M G B deg hB q a ha i hi
end GradedBasisAcceptance
