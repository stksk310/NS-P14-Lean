module
public import NSP14.Lex.ElementaryDistraction
@[expose] public section
open scoped Classical
namespace NSP14.Tests.ElementaryDistraction
variable (k : Type) [Field k] (q : ℕ)

theorem actual_single_factor_change (a b : Fin q) (m : ℕ) (α : Fin q →₀ ℕ) (hm : m<α b) :
    Lex.distractionMonomial k q
      (fun i j => if i=b ∧ j=m then MvPolynomial.X b+MvPolynomial.X a else MvPolynomial.X i) α=
      MvPolynomial.monomial α (1:k)+MvPolynomial.monomial (Lex.raisedExponent q α a b) (1:k) :=
  Lex.elementaryDistraction_active k q a b m α hm
end NSP14.Tests.ElementaryDistraction
