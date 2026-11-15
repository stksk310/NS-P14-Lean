module
public import NSP14.Lex.EliahouKervaire
@[expose] public section
namespace NSP14.Tests.LexGradedStep
theorem actual_graded_step (k : Type) [Field k] (q : ℕ)
    (L : Ideal (MvPolynomial (Fin q) k)) (hproper : L ≠ ⊤) (hL : Lex.IsLex k q L)
    (w : Fin q →₀ ℕ) (hw : Lex.MinimalGenerator k q L w) (i : ℕ) (t : ℤ) :
    Lex.quotientGradedBetti k q (Lex.predecessorIdeal k q L w ⊔ Ideal.span {MvPolynomial.monomial w (1:k)})
        (Lex.predecessor_adjoin_homogeneous k q L w) (i+1) t=
      Lex.quotientGradedBetti k q (Lex.predecessorIdeal k q L w)
        (Lex.predecessor_homogeneous k q L w) (i+1) t+
      Lex.quotientGradedBetti k q (Lex.beforeVariableIdeal k q w)
        (Lex.beforeVariableIdeal_homogeneous k q w) i (t-(w.degree:ℤ)) :=
  Lex.IsLex.predecessor_graded_step k q hL hproper w hw i t
end NSP14.Tests.LexGradedStep
