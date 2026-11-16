module
public import audit.run18.BHPEKClosedGoals
public import audit.run18.EdgeClosedGoals
public import audit.run18.DenseClosedGoals
public import audit.run18.PartialClosedGoals
public import audit.run18.FiveClosedGoals
public import NSP14.Width.Closure
@[expose] public section
namespace NSP14.Run18
/-- Every original physical narrow width, coefficient field and actual completed Betti row. -/
theorem width_closed : Requested.W_CLOSE := by
  intro S k _ he hw
  exact S.narrow_width_comparison k he hw

/-- All six assigned frozen obligations, with their original quantified input types. -/
theorem all_closed : Requested.X_BHP_EK ∧ Requested.W_EDGE ∧ Requested.W_DENSE ∧
    Requested.W_SPARSE ∧ Requested.W_FIVE ∧ Requested.W_CLOSE :=
  ⟨NSP14.Lex.bhp_ek,edge_closed,dense_closed,sparse_closed,five_closed,width_closed⟩
end NSP14.Run18
