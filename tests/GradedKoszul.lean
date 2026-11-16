module

public import NSP14
public import tests.Run13Fixtures

@[expose] public section
open NSP14.Homological
namespace GradedKoszulAcceptance
abbrev k := ZMod 2
abbrev L := RatFunc k
open Run12Fixtures

theorem jump_shift (i : ℕ) (t : ℤ) :
    gradedBetti k changing.NonXAtom _ (changing.descendingStratumGrading k 2) i t =
      gradedBetti k changing.NonXAtom _ (changing.ascendingStratumGrading k 2 (by decide)) i (t+2) :=
  changing.jumpStratum_gradedBetti k 2 (by decide) i t

theorem actualG_graded_extension (i : ℕ) (t : ℤ) :
    extendedGradedBetti k L changing.AtomExponent _ (changing.fullGGrading k) i t =
      gradedBetti k changing.AtomExponent _ (changing.fullGGrading k) i t :=
  gradedBetti_baseChange k L changing.AtomExponent _ (changing.fullGGrading k) i t
end GradedKoszulAcceptance
