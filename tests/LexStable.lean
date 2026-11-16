module
public import NSP14.Lex.MonomialGenerators
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
namespace NSP14.Tests.LexStable

theorem actual_lex_raise (k : Type) [Field k] (q : ℕ)
    (L : Ideal (MvPolynomial (Fin q) k)) (hL : Lex.IsLex k q L)
    (v : Fin q →₀ ℕ) (hv : MvPolynomial.monomial v (1:k)∈L)
    (i j : Fin q) (hj : 0<v j) (hij : i<j) :
    MvPolynomial.monomial (Lex.raisedExponent q v i j) (1:k)∈L :=
  hL.raise k q v hv i j hj hij

theorem actual_minimal_divisor (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k)) (v : Fin q →₀ ℕ)
    (hv : MvPolynomial.monomial v (1:k)∈I) :
    ∃ w : Fin q →₀ ℕ,w ≤ v ∧ Lex.MinimalGenerator k q I w := Lex.minimal_divisor k q I v hv

theorem actual_finite_minimal_generators (k : Type) [Field k] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k)) :
    ∀ v,v∈Lex.minimalGeneratorFinset k q I ↔ Lex.MinimalGenerator k q I v :=
  Lex.mem_minimalGeneratorFinset k q I
end NSP14.Tests.LexStable
