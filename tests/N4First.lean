module
public import NSP14.NarrowFour.FirstLarge
@[expose] public section
open NSP14
example (D : Endpoint.Data) (a b : D.a) (hab : a.val<b.val) :
    ¬NarrowFour.Standard D a b (b.val,0) := NarrowFour.first_pure_relation D a b hab

example (D : Endpoint.Data) (k : Type) [Field k] (hq : D.q=2) (a b : D.a)
    (hab : NarrowFour.OrderedPair D a b) := NarrowFour.first_count D k hq a b hab
example (u : ℕ) (hu : 9 ≤ u) := NarrowFour.first_large_payment u hu
example (D : Endpoint.Data) (k : Type) [Field k] (hq : D.q=2) (hu : D.u=5) :
    Homological.totalBetti k D.Variables (D.fullG k) 1 ≤ 11 :=
  NarrowFour.actual_first_five D k hq hu
example : (NarrowFour.positiveTriangle 4).card=6 := by
  rw [NarrowFour.positiveTriangle_card];decide
example : (NarrowFour.removedTriangle 4 1 3).card=1 := by
  rw [NarrowFour.removedTriangle_card];decide
example : (NarrowFour.removedTriangle 4 1 4).card=0 := by
  rw [NarrowFour.removedTriangle_card];decide
example : (NarrowFour.removedTriangle 4 1 2).card=3 := by
  rw [NarrowFour.removedTriangle_card];decide
