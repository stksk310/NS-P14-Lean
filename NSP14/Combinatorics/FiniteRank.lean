module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped Classical BigOperators

namespace NSP14

variable {ι : Type*} [Fintype ι]

noncomputable def lowerRankSet (f : ι → ℕ) (a : ι) : Finset ι :=
  Finset.univ.filter (fun b => f b < f a)

noncomputable def lowerRank (f : ι → ℕ) (a : ι) : ℕ := (lowerRankSet f a).card

theorem lowerRank_lt_card (f : ι → ℕ) (a : ι) : lowerRank f a < Fintype.card ι := by
  have hs : lowerRankSet f a ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro he
    have ha : a ∈ lowerRankSet f a := he.symm ▸ Finset.mem_univ a
    exact (Nat.lt_irrefl _ (Finset.mem_filter.mp ha).2)
  simpa only [lowerRank, Finset.card_univ] using Finset.card_lt_card hs

theorem lowerRank_strict (f : ι → ℕ) {a b : ι} (h : f a < f b) : lowerRank f a < lowerRank f b := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2.trans h⟩
  · intro he
    have ha : a ∈ lowerRankSet f b := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    rw [← he] at ha
    exact Nat.lt_irrefl _ (Finset.mem_filter.mp ha).2

theorem lowerRank_injective {f : ι → ℕ} (hf : Function.Injective f) : Function.Injective (lowerRank f) := by
  intro a b he
  apply hf
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have := lowerRank_strict f h; omega
  · have := lowerRank_strict f h; omega

noncomputable def lowerRankEquiv {f : ι → ℕ} (hf : Function.Injective f) : ι ≃ Fin (Fintype.card ι) :=
  Equiv.ofBijective (fun a => ⟨lowerRank f a, lowerRank_lt_card f a⟩)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨fun _ _ he => lowerRank_injective hf
      (congrArg Fin.val he), by simp⟩)

@[simp] theorem lowerRankEquiv_val {f : ι → ℕ} (hf : Function.Injective f) (a : ι) :
    (lowerRankEquiv hf a).val = lowerRank f a := rfl

end NSP14
