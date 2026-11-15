module
public import NSP14.Lex.StrongStableOperations
@[expose] public section
namespace NSP14.Tests.StrongStableOperations
variable (k : Type) [Field k] (q : ℕ)

theorem actual_regressive_substitution (I : Ideal (MvPolynomial (Fin q) k))
    (hI : Lex.IsStronglyStable k q I) (f : Fin q → Fin q) (hf : ∀ i, f i ≤ i)
    (α γ : Fin q →₀ ℕ) (hm : MvPolynomial.monomial (γ+α) (1:k)∈I) :
    MvPolynomial.monomial (γ+α.mapDomain f) (1:k)∈I :=
  Lex.IsStronglyStable.regressive_substitution k q I hI f hf α γ hm
end NSP14.Tests.StrongStableOperations
