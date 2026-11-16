module

public import NSP14
public import tests.Run13Fixtures

@[expose] public section
open NSP14.Homological
namespace ActualGradedBaseChangeAcceptance
abbrev k := ZMod 2
abbrev L := RatFunc k
open Run12Fixtures

/-- Both sides use their independently constructed actual order gradings. -/
theorem changing_G (i : ℕ) (t : ℤ) :
    gradedBetti L changing.AtomExponent _ (changing.fullGGrading L) i t =
      gradedBetti k changing.AtomExponent _ (changing.fullGGrading k) i t :=
  changing.actualG_gradedBetti_baseChange k L i t

theorem changing_T (i : ℕ) (t : ℤ) :
    gradedBetti L changing.NonXAtom _ (changing.actualTGrading L) i t =
      gradedBetti k changing.NonXAtom _ (changing.actualTGrading k) i t :=
  changing.actualT_gradedBetti_baseChange k L i t

theorem changing_A (i : ℕ) (t : ℤ) :
    gradedBetti L changing.NonXAtom _ (changing.actualAGrading L) i t =
      gradedBetti k changing.NonXAtom _ (changing.actualAGrading k) i t :=
  changing.actualA_gradedBetti_baseChange k L i t

theorem changing_N (i : ℕ) (t : ℤ) :
    gradedBetti L changing.NonXAtom _ (changing.actualNGrading L) i t =
      gradedBetti k changing.NonXAtom _ (changing.actualNGrading k) i t :=
  changing.actualN_gradedBetti_baseChange k L i t

theorem changing_Q (i : ℕ) (t : ℤ) :
    gradedBetti L changing.NonXAtom _ (changing.actualQGrading L) i t =
      gradedBetti k changing.NonXAtom _ (changing.actualQGrading k) i t :=
  changing.actualQ_gradedBetti_baseChange k L i t
end ActualGradedBaseChangeAcceptance
