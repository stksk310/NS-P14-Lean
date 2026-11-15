module
public import NSP14.Homological.GradedKoszulExact
@[expose] public section
open CategoryTheory
namespace NSP14.Tests.GradedKoszulExact
theorem actual_graded_sequence (k σ : Type) [Field k]
    (S : ShortComplex (ModuleCat (Homological.VariableRing k σ))) (hS : S.ShortExact)
    (G1 : Homological.GradedPolynomialModule k σ S.X₁)
    (G2 : Homological.GradedPolynomialModule k σ S.X₂)
    (G3 : Homological.GradedPolynomialModule k σ S.X₃)
    (hf : ∀ q (a : Homological.coefficientModule k σ S.X₁),a ∈ G1.degreeSpace q → S.f a ∈ G2.degreeSpace q)
    (hg : ∀ q (a : Homological.coefficientModule k σ S.X₂),a ∈ G2.degreeSpace q → S.g a ∈ G3.degreeSpace q)
    (xs : List σ) (t : ℤ) :
    (Homological.gradedKoszulSequence k σ S G1 G2 G3 hf hg xs t).ShortExact :=
  Homological.gradedKoszulSequence_shortExact k σ S G1 G2 G3 hf hg hS xs t

theorem actual_graded_betti_additivity (k σ : Type) [Field k] [Fintype σ]
    (S : ShortComplex (ModuleCat (Homological.VariableRing k σ))) (hS : S.ShortExact)
    [Module.Finite (Homological.VariableRing k σ) S.X₁]
    [Module.Finite (Homological.VariableRing k σ) S.X₂]
    [Module.Finite (Homological.VariableRing k σ) S.X₃]
    (G1 : Homological.GradedPolynomialModule k σ S.X₁)
    (G2 : Homological.GradedPolynomialModule k σ S.X₂)
    (G3 : Homological.GradedPolynomialModule k σ S.X₃)
    (hf : ∀ q (a : Homological.coefficientModule k σ S.X₁),a ∈ G1.degreeSpace q → S.f a ∈ G2.degreeSpace q)
    (hg : ∀ q (a : Homological.coefficientModule k σ S.X₂),a ∈ G2.degreeSpace q → S.g a ∈ G3.degreeSpace q)
    (hz : ∀ j,HomologicalComplex.homologyMap ((Homological.coefficientKoszulFunctor k σ).map S.f) j=0)
    (i : ℕ) (t : ℤ) :
    Homological.gradedBetti k σ S.X₃ G3 (i+1) t=
      Homological.gradedBetti k σ S.X₂ G2 (i+1) t+Homological.gradedBetti k σ S.X₁ G1 i t :=
  Homological.graded_quotient_betti_additivity k σ S G1 G2 G3 hf hg hS hz i t
end NSP14.Tests.GradedKoszulExact
