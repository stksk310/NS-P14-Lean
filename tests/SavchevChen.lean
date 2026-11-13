module
public import NSP14.Additive.SavchevChen
@[expose] public section
open scoped BigOperators
open NSP14.Additive
theorem Run17_SC_contract (u ℓ : ℕ) (hu : 2 ≤ u) (seq : Fin ℓ → ZMod u)
    (hz : ZeroSumFree seq) (hl : u < 2*ℓ) :
    ∃ c : (ZMod u)ˣ, ∑ i, ((c : ZMod u)*seq i).val < u :=
  savchevChen hu seq hz hl
