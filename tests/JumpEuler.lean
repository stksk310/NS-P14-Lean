module
public import NSP14
@[expose] public section
namespace JumpEulerAcceptance
open NSP14
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)
theorem actual_step (s j : ℕ) (hs : 0 < s) :
    C.descendingEuler s j ≤ C.descendingEuler (s+1) j+C.cutKEuler s j :=
  C.descendingEuler_step s hs j
theorem actual_T_sum (j : ℕ) :
    C.cutTEuler j ≤ ∑ t ∈ Finset.range (S.qTopDegree-1),C.cutKEuler (2+t) j :=
  C.cutTEuler_le_sum j
end JumpEulerAcceptance
