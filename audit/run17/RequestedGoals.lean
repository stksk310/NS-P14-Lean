module
public import NSP14.Additive.Stabilizer
public import NSP14.Additive.ZeroSumSequence
@[expose] public section
open scoped Pointwise BigOperators
namespace NSP14.Run17.Requested
/-- Frozen general finite-abelian-group goal. No periodicity hypothesis is added. -/
def Kneser : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G), A.Nonempty → B.Nonempty →
    let H := Additive.sumStabilizer (A+B)
    (Additive.thicken A H).card + (Additive.thicken B H).card ≤
      (A+B).card + Nat.card H
/-- Frozen general positional-sequence goal, including composite moduli. -/
def SavchevChen : Prop :=
  ∀ (u : ℕ), 2 ≤ u → ∀ (ℓ : ℕ) (seq : Fin ℓ → ZMod u),
    Additive.ZeroSumFree seq → u < 2*ℓ →
    ∃ c : (ZMod u)ˣ, ∑ i : Fin ℓ, ((c : ZMod u)*seq i).val < u
end NSP14.Run17.Requested
