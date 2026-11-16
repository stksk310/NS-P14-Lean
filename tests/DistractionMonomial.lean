module
public import NSP14.Lex.DistractionMonomial
@[expose] public section
open scoped BigOperators
namespace NSP14.Tests.DistractionMonomial
theorem actual_distraction_step (R : Type) [CommRing R] (q : ℕ)
    (L : Fin q → ℕ → MvPolynomial (Fin q) R) (a : Fin q →₀ ℕ) (i : Fin q) :
    (∏ x : Fin q,∏ j ∈ Finset.range ((a+Finsupp.single i 1 : Fin q →₀ ℕ) x),L x j)=
      L i (a i)*(∏ x : Fin q,∏ j ∈ Finset.range (a x),L x j) :=
  Lex.distractionMonomial_step R q L a i
end NSP14.Tests.DistractionMonomial
