module
public import NSP14.Lex.PrefixVariableRestriction
@[expose] public section
namespace NSP14.Tests.PrefixVariableRestriction
variable (k : Type) [Field k] (q d r : ℕ)
theorem actual_prefix_counts (I L : Ideal (MvPolynomial (Fin q) k))
    (hI : Lex.IsStronglyStable k q I) (hL : Lex.IsLex k q L)
    (hc : Lex.idealDegreeCard k q L d≤Lex.idealDegreeCard k q I d) :
    Lex.cumulativeDegreeCard k q L d r≤Lex.cumulativeDegreeCard k q I d r :=
  Lex.IsStronglyStable.cumulative_le_lex k q I L hI hL d hc r
end NSP14.Tests.PrefixVariableRestriction
