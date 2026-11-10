module
import NSP14.Semigroup.OffsetStabilization
open NSP14
open NSP14.NumericalSemigroup
example (S : NumericalSemigroup) (r : Fin S.multiplicity) (q : ℕ)
    (hq : S.leastOffsetLength r ≤ S.offsetLevel r + q) :
    S.order (S.apery r + q * S.multiplicity) = S.offsetLevel r + q :=
  S.order_stabilization r q hq
example (S : NumericalSemigroup) : Set.Finite {x | S.Terminal x} :=
  S.terminal_finite
