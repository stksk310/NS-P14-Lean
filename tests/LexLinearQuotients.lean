module
public import NSP14.Lex.EliahouKervaireStep
@[expose] public section
namespace NSP14.Tests.LexLinearQuotients
theorem actual_lex_colon (k : Type) [Field k] (q : ℕ)
    (L : Ideal (MvPolynomial (Fin q) k)) (hL : Lex.IsLex k q L)
    (w : Fin q →₀ ℕ) (hw : Lex.MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ i, r < i → w i=0) :
    (Lex.predecessorIdeal k q L w).colon {MvPolynomial.monomial w (1:k)} =
      Ideal.span (MvPolynomial.X '' {i : Fin q | i < r}) :=
  Lex.IsLex.predecessor_colon k q hL w hw r hr hmax

theorem actual_betti_step (k : Type) [Field k] (q : ℕ)
    (L : Ideal (MvPolynomial (Fin q) k)) (hL : Lex.IsLex k q L)
    (w : Fin q →₀ ℕ) (hw : Lex.MinimalGenerator k q L w)
    (r : Fin q) (hr : 0 < w r) (hmax : ∀ j, r < j → w j=0) (i : ℕ) :
    let J := Lex.predecessorIdeal k q L w
    Homological.totalBetti k (Fin q)
      (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ (J ⊔ Ideal.span {MvPolynomial.monomial w (1:k)}))) (i+1)=
      Homological.totalBetti k (Fin q)
        (ModuleCat.of (MvPolynomial (Fin q) k) ((MvPolynomial (Fin q) k) ⧸ J)) (i+1)+
      Homological.totalBetti k (Fin q)
        (ModuleCat.of (MvPolynomial (Fin q) k)
          ((MvPolynomial (Fin q) k) ⧸ Ideal.span ((MvPolynomial.X : Fin q → MvPolynomial (Fin q) k) '' {j : Fin q | j < r}))) i :=
  Lex.IsLex.predecessor_betti_step k q hL w hw r hr hmax i
end NSP14.Tests.LexLinearQuotients
