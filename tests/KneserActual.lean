module
public import NSP14.Additive.Kneser
public import NSP14.Additive.KneserIterated
@[expose] public section
open scoped Pointwise Classical
open NSP14.Additive
theorem Run17_kneser_contract (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) :
    (thicken A (sumStabilizer (A+B))).card +
      (thicken B (sumStabilizer (A+B))).card ≤
      (A+B).card + Nat.card (sumStabilizer (A+B)) := kneser A B hA hB

namespace Run17Kneser
def A8 : Finset (ZMod 8) := {0,1,4,5}
theorem sum8 : A8+A8 = {0,1,2,4,5,6} := by decide
theorem stabilizer8 : (sumStabilizer (A8+A8) : Set (ZMod 8)).toFinset = {0,4} := by
  rw [stabilizer_toFinset (by decide)]
  decide
theorem stabilizer8_card : Nat.card (sumStabilizer (A8+A8))=2 := by
  rw [stabilizer_card (by decide)]
  decide
theorem corrected_bound8 : (thicken A8 (sumStabilizer (A8+A8))).card+
    (thicken A8 (sumStabilizer (A8+A8))).card = (A8+A8).card+2 := by
  unfold thicken
  rw [stabilizer8]
  decide
theorem uncorrected_bound8_false : ¬7 ≤ (A8+A8).card := by decide
theorem singleton_kneser (a : ZMod 8) (B : Finset (ZMod 8)) (hB : B.Nonempty) :
    let H := sumStabilizer ({a}+B)
    (thicken {a} H).card+(thicken B H).card ≤ ({a}+B).card+Nat.card H :=
  kneser {a} B (Finset.singleton_nonempty a) hB
theorem prime_kneser :
    let A : Finset (ZMod 5) := {0,1}
    let B : Finset (ZMod 5) := {0,2,4}
    let H := sumStabilizer (A+B)
    (thicken A H).card+(thicken B H).card ≤ (A+B).card+Nat.card H :=
  kneser ({0,1} : Finset (ZMod 5)) {0,2,4} ⟨0,by simp⟩ ⟨0,by simp⟩
theorem full_kneser (u : ℕ) [NeZero u] :
    let A : Finset (ZMod u) := Finset.univ
    let H := sumStabilizer (A+A)
    (thicken A H).card+(thicken A H).card ≤ (A+A).card+Nat.card H :=
  kneser (Finset.univ : Finset (ZMod u)) Finset.univ ⟨0,Finset.mem_univ 0⟩ ⟨0,Finset.mem_univ 0⟩
theorem full_group (u : ℕ) [NeZero u] :
    (thicken (Finset.univ : Finset (ZMod u)) (sumStabilizer Finset.univ)).card ≤ u :=
  (Finset.card_le_univ _).trans_eq (ZMod.card u)
theorem trivial_group : (thicken ({0} : Finset (ZMod 1))
    (sumStabilizer ({0}+{0} : Finset (ZMod 1)))).card = 1 := by
  apply le_antisymm
  · exact Finset.card_le_univ _
  · exact Finset.card_pos.mpr ⟨0,subset_thicken _ _ (by simp)⟩
end Run17Kneser
