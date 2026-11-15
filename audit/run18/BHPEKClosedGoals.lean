module
public import audit.run18.RequestedGoals
public import NSP14.Lex.BettiComparison
@[expose] public section
namespace NSP14.Lex
/-- The original frozen BHP and EK contracts, without restrictions on the coefficient field. -/
theorem bhp_ek : NSP14.Run18.Requested.X_BHP_EK := by
  constructor
  · intro k _ q I L hI hL hLex hH i hi t
    exact quotientGradedBetti_le_lex k q I L hI hL hLex hH i hi t
  · intro k _ q L hHom hproper hLex g hg i hi t
    exact hLex.graded_ek k q hproper hHom g hg i hi t
end NSP14.Lex
