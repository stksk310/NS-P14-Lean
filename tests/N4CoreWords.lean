module
public import NSP14.NarrowFour.CoreWords
@[expose] public section
open NSP14
example (D : Endpoint.Data) (k : Type) [Field k] (a b : D.a)
    (hab : NarrowFour.OrderedPair D a b) :
    D.coreP k=(NarrowFour.standardWords D a b).card :=
  NarrowFour.coreP_card D k a b hab
