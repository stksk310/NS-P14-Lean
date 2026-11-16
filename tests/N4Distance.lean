module
public import NSP14.NarrowFour.Distance
@[expose] public section
open NSP14
example (D : Endpoint.Data) (k : Type) [Field k] (hq : D.q=2) (a b : D.a)
    (hab : NarrowFour.OrderedPair D a b) :
    (D.internalSigma k hq+1).choose 2≤D.coreP k :=
  NarrowFour.socle_triangle_card D k hq a b hab
