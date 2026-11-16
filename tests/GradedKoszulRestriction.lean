module
public import NSP14.Homological.GradedKoszulMap
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Tests.GradedKoszulRestriction
theorem actual_piece_injective (k σ : Type) [Field k]
    (M : ModuleCat (Homological.VariableRing k σ))
    (G : Homological.GradedPolynomialModule k σ M) (xs : List σ) (t : ℤ) (i : ℕ) :
    Function.Injective (homologyMap (Homological.gradedKoszulInclusion k σ M G xs t) i) :=
  Homological.gradedKoszulHomologyInclusion_injective k σ M G xs t i

theorem actual_degree_zero (k σ : Type) [Field k]
    (M N : ModuleCat (Homological.VariableRing k σ))
    (G : Homological.GradedPolynomialModule k σ M) (H : Homological.GradedPolynomialModule k σ N)
    (f : M ⟶ N) (s : ℤ)
    (hf : ∀ q (a : Homological.coefficientModule k σ M),a ∈ G.degreeSpace q → f a ∈ H.degreeSpace (q+s))
    (xs : List σ) (t : ℤ) (i : ℕ)
    (hz : homologyMap ((Homological.coefficientKoszulListFunctor k σ xs).map f) i=0) :
    homologyMap (Homological.gradedKoszulMap k σ G H f s hf xs t) i=0 :=
  Homological.gradedKoszulMap_homology_zero k σ G H f s hf xs t i hz

theorem actual_degree_projection_natural (k σ : Type) [Field k]
    (M N : ModuleCat (Homological.VariableRing k σ))
    (G : Homological.GradedPolynomialModule k σ M) (H : Homological.GradedPolynomialModule k σ N)
    (f : M ⟶ N) (s : ℤ)
    (hf : ∀ q (a : Homological.coefficientModule k σ M),a ∈ G.degreeSpace q → f a ∈ H.degreeSpace (q+s))
    (xs : List σ) (t : ℤ) :
    (Homological.coefficientKoszulListFunctor k σ xs).map f ≫
        Homological.gradedKoszulRetraction k σ N H xs (t+s)=
      Homological.gradedKoszulRetraction k σ M G xs t ≫
        Homological.gradedKoszulMap k σ G H f s hf xs t :=
  Homological.gradedKoszulMap_retraction k σ G H f s hf xs t
end NSP14.Tests.GradedKoszulRestriction
