module
public import NSP14.Lex.PrefixDominance
@[expose] public section
namespace NSP14.Tests.PrefixDominance
variable (k : Type) [Field k] (q : ℕ)

theorem actual_stable_tail_transfer (I : Ideal (MvPolynomial (Fin (q+1)) k))
    (hI : Lex.IsStronglyStable k (q+1) I) (α β : Fin (q+1) →₀ ℕ)
    (hdeg : α.degree=β.degree)
    (hdom : ∀ t,t≤q+1 → Lex.reversedPrefix q β t≤Lex.reversedPrefix q α t)
    (hmem : MvPolynomial.monomial α (1:k)∈I) : MvPolynomial.monomial β (1:k)∈I :=
  Lex.IsStronglyStable.mem_of_tail_le k q I hI α β hdeg hdom hmem
end NSP14.Tests.PrefixDominance
