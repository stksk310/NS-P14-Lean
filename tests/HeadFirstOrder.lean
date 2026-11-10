module
public import NSP14.Semigroup.HeadFirstOrderCoordinates
public import tests.Run14Fixtures
public import Mathlib.Algebra.Field.ZMod
@[expose] public section
namespace HeadFirstOrderAcceptance
open NSP14 NSP14.NumericalSemigroup

theorem actual_B_length : Module.finrank (ZMod 2)
    (Run14Fixtures.rankTwo.source.FirstOrderHead (ZMod 2))=3 := by
  rw [Run14Fixtures.rankTwo.source.firstOrderHead_finrank (ZMod 2),Run14Fixtures.rankTwo.embedding]

end HeadFirstOrderAcceptance
