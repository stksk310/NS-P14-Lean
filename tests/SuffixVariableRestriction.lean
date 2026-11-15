module
public import NSP14.Lex.SuffixVariableRestriction
@[expose] public section
namespace NSP14.Tests.SuffixVariableRestriction
variable (k : Type) [Field k] (s r : ℕ)
theorem actual_last_variables_lex (I : Ideal (MvPolynomial (Fin (s+r)) k)) (hI : Lex.IsLex k (s+r) I) :
    Lex.IsLex k r (Lex.suffixVariableIdeal k s r I) := Lex.suffixVariableIdeal_isLex k s r I hI
end NSP14.Tests.SuffixVariableRestriction
