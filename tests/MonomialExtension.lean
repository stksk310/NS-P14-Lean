module
public import NSP14.Lex.MonomialExtension
@[expose] public section
open scoped Classical
namespace NSP14.Tests.MonomialExtension
theorem actual_ringmap_ideal (k L : Type) [Field k] [Field L] [Algebra k L] (q : ℕ)
    (I : Ideal (MvPolynomial (Fin q) k)) (hmono : Lex.IsMonomial k q I) :
    ∃ J : Ideal (MvPolynomial (Fin q) L),
      (∀ a : Fin q →₀ ℕ, MvPolynomial.monomial a (1:L)∈J ↔ MvPolynomial.monomial a (1:k)∈I) ∧
      J=I.map (MvPolynomial.map (algebraMap k L)) :=
  ⟨Lex.monomialExtension k L q I,Lex.monomialExtension_mem_iff k L q I,
    Lex.monomialExtension_eq_map k L q I hmono⟩
end NSP14.Tests.MonomialExtension
