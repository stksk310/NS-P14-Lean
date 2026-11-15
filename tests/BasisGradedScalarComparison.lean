module
public import NSP14.Homological.BasisGradedScalarComparison
public import NSP14.Homological.HomogeneousBasisPieces
@[expose] public section
open scoped Classical TensorProduct
open CategoryTheory NSP14.Homological
namespace NSP14.Tests.BasisGradedScalarComparison
theorem actual_basis_degree_comparison (k L σ : Type) [Field k] [Field L] [Algebra k L]
    (M : ModuleCat (VariableRing k σ)) (N : ModuleCat (VariableRing L σ))
    (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule L σ N) {J : Type}
    (b : Module.Basis J k (coefficientModule k σ M))
    (c : Module.Basis J L (coefficientModule L σ N)) (deg : J → ℤ)
    (hb : ∀ j,b j∈G.degreeSpace (deg j)) (hc : ∀ j,c j∈H.degreeSpace (deg j))
    (e : polynomialBaseChangeModule k L σ M ≅ N)
    (he : ∀ j,(show coefficientModule L σ N from e.hom ((1:L) ⊗ₜ[k] b j))=c j) :
    Nonempty (GradedScalarComparison k L σ G H e) :=
  ⟨basisGradedScalarComparison k L σ M N G H b c deg hb hc e he⟩
end NSP14.Tests.BasisGradedScalarComparison
