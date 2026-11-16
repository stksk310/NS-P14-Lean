module
public import NSP14.Additive.KneserCore
public import NSP14.Additive.Stabilizer
@[expose] public section
open scoped Pointwise
open scoped Classical
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
theorem stabilizer_toFinset {S : Finset G} (hS : S.Nonempty) :
    (sumStabilizer S : Set G).toFinset = S.addStab := by
  ext g
  rw [Set.mem_toFinset, Finset.mem_addStab hS]
  exact mem_sumStabilizer S g
theorem stabilizer_card {S : Finset G} (hS : S.Nonempty) :
    Nat.card (sumStabilizer S) = S.addStab.card := by
  rw [←stabilizer_toFinset hS]
  exact Nat.card_eq_fintype_card.trans (Set.toFinset_card _).symm
/-- Full thickening form, with the actual translation stabilizer of A+B. -/
theorem kneser (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) :
    (thicken A (sumStabilizer (A+B))).card +
      (thicken B (sumStabilizer (A+B))).card ≤
      (A+B).card + Nat.card (sumStabilizer (A+B)) := by
  simpa only [thicken, stabilizer_toFinset (hA.add hB), stabilizer_card (hA.add hB)] using
    Finset.add_kneser A B
end NSP14.Additive
