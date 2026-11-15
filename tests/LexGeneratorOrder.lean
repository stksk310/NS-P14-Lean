module
public import NSP14.Lex.GeneratorOrder
@[expose] public section
namespace NSP14.Tests.LexGeneratorOrder
theorem actual_finite_order (k : Type) [Field k] (q : ℕ)
    (L : Ideal (MvPolynomial (Fin q) k)) :
    (Lex.generatorList q k L).toFinset=Lex.minimalGeneratorFinset k q L ∧
      (Lex.generatorList q k L).Pairwise (Lex.precedes q) :=
  ⟨Lex.generatorList_toFinset q k L,Lex.generatorList_pairwise q k L⟩

theorem actual_previous_generators (k : Type) [Field k] (q : ℕ)
    (L : Ideal (MvPolynomial (Fin q) k)) (w : Fin q →₀ ℕ) :
    Lex.predecessorIdeal k q L w =
      Ideal.span ((fun v => MvPolynomial.monomial v (1:k)) ''
        {v | Lex.MinimalGenerator k q L v ∧ Lex.precedes q v w}) :=
  Lex.predecessorIdeal_minimal q k L w
end NSP14.Tests.LexGeneratorOrder
