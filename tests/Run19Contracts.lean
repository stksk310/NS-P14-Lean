module
public import audit.run19.RequestedGoals
@[expose] public section
#check NSP14.Run19.Requested.N_DISTANCE
#check NSP14.Run19.Requested.N_WORDS
#check NSP14.Run19.Requested.N_HIGH
#check NSP14.Run19.Requested.N_FIRST
#check NSP14.Run19.Requested.N_SMALL
#check NSP14.Run19.Requested.N_WIDTH4
#check NSP14.Run19.Requested.N_CLOSE
#check NSP14.Run19.Requested.I_BASE
#check NSP14.Run19.Requested.X_LTV
#check NSP14.Run19.Requested.I_THREE
example (S : NSP14.NumericalSemigroup) : S.intervalCompletionAll.carrier=
    AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom) := rfl
