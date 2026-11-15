module
public import audit.run18.RequestedGoals
public import NSP14.Lex.EliahouKervaire
@[expose] public section
namespace NSP14.Run18
/-- The frozen EK conjunct, including its actual internal-degree shift, over every field. -/
theorem ek_closed : Requested.EK := by
  intro k _ q L hHom hproper hLex g hg i hi t
  exact hLex.graded_ek k q hproper hHom g hg i hi t
end NSP14.Run18
