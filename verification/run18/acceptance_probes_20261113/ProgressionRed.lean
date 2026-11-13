module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
example (d s k b N : ℕ) (hs : 0<s) (hN : k<N) (hd : d=s*k+b) (hb : b<s) :
    2*(∑ j∈Finset.range N,(d-s*j)) = s*k*(k+1)+2*b*(k+1) :=
  NSP14.Width.progression_sum d s k b N hs hN hd hb
