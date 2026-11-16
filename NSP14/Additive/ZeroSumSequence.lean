module
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
@[expose] public section
open scoped BigOperators
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G]
/-- Positions are selected, so equal terms retain their multiplicities. -/
def ZeroSumFree {ℓ : ℕ} (seq : Fin ℓ → G) : Prop :=
  ∀ I : Finset (Fin ℓ), I.Nonempty → ∑ i ∈ I, seq i ≠ 0
instance decidableZeroSumFree [DecidableEq G] {ℓ : ℕ} (seq : Fin ℓ → G) :
    Decidable (ZeroSumFree seq) := by
  unfold ZeroSumFree
  infer_instance
theorem zeroSumFree_empty (seq : Fin 0 → G) : ZeroSumFree seq := by
  intro I hI
  obtain ⟨i,_⟩ := hI
  exact i.elim0
theorem ZeroSumFree.term_ne_zero {ℓ : ℕ} {seq : Fin ℓ → G}
    (h : ZeroSumFree seq) (i : Fin ℓ) : seq i ≠ 0 := by
  simpa using h {i} (Finset.singleton_nonempty i)

theorem ZeroSumFree.comp {ℓ m : ℕ} {seq : Fin ℓ → G}
    (h : ZeroSumFree seq) (f : Fin m → Fin ℓ) (hf : Function.Injective f) :
    ZeroSumFree (seq ∘ f) := by
  intro I hI
  have hi := h (I.image f) (hI.image f)
  simpa only [Finset.sum_image (fun _ _ _ _ he => hf he), Function.comp_def] using hi

theorem zeroSumFree_reindex_iff {ℓ m : ℕ} (seq : Fin ℓ → G) (e : Fin m ≃ Fin ℓ) :
    ZeroSumFree (seq ∘ e) ↔ ZeroSumFree seq := by
  constructor
  · intro h
    simpa [Function.comp_def] using h.comp e.symm e.symm.injective
  · intro h
    exact h.comp e e.injective

theorem ZeroSumFree.map {H : Type*} [AddCommGroup H] {ℓ : ℕ} {seq : Fin ℓ → G}
    (h : ZeroSumFree seq) (f : G →+ H) (hf : Function.Injective f) :
    ZeroSumFree (f ∘ seq) := by
  intro I hI he
  apply h I hI
  apply hf
  simpa only [map_sum, map_zero, Function.comp_def] using he

theorem ZeroSumFree.sum_ne_sum_of_ssubset {ℓ : ℕ} {seq : Fin ℓ → G}
    (h : ZeroSumFree seq) {I J : Finset (Fin ℓ)} (hIJ : I ⊂ J) :
    ∑ i ∈ I, seq i ≠ ∑ i ∈ J, seq i := by
  intro he
  have hn : (J \ I).Nonempty := Finset.sdiff_nonempty.mpr hIJ.not_ge
  apply h (J \ I) hn
  have hs := Finset.sum_sdiff hIJ.subset (f := seq)
  rw [←he] at hs
  exact add_right_cancel (hs.trans (zero_add _).symm)

/-- The positions strictly before j, allowing j=ℓ as the final prefix. -/
def prefixPositions (ℓ : ℕ) (j : Fin (ℓ+1)) : Finset (Fin ℓ) :=
  Finset.univ.filter (fun i => i.val < j.val)

theorem prefixPositions_ssubset {ℓ : ℕ} {i j : Fin (ℓ+1)} (hij : i < j) :
    prefixPositions ℓ i ⊂ prefixPositions ℓ j := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro k hk
    simp only [prefixPositions, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans hij
  · intro he
    have hi : i.val < ℓ := by have := j.isLt; change i.val < j.val at hij; omega
    have hm : (⟨i.val,hi⟩ : Fin ℓ) ∈ prefixPositions ℓ j := by
      simpa only [prefixPositions, Finset.mem_filter, Finset.mem_univ, true_and] using
        (show i.val < j.val from hij)
    rw [←he] at hm
    simp [prefixPositions] at hm

theorem ZeroSumFree.prefixSum_injective {ℓ : ℕ} {seq : Fin ℓ → G}
    (h : ZeroSumFree seq) :
    Function.Injective (fun j : Fin (ℓ+1) => ∑ i ∈ prefixPositions ℓ j, seq i) := by
  intro i j he
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (h.sum_ne_sum_of_ssubset (prefixPositions_ssubset hij) he)
  · exact hij
  · exact False.elim (h.sum_ne_sum_of_ssubset (prefixPositions_ssubset hij) he.symm)

theorem ZeroSumFree.length_lt_card [Fintype G] {ℓ : ℕ} {seq : Fin ℓ → G}
    (h : ZeroSumFree seq) : ℓ < Fintype.card G := by
  have hi := Fintype.card_le_of_injective _ h.prefixSum_injective
  simpa using hi

theorem ZeroSumFree.length_lt_modulus {u ℓ : ℕ} [NeZero u] {seq : Fin ℓ → ZMod u}
    (h : ZeroSumFree seq) : ℓ < u := by
  simpa only [ZMod.card] using h.length_lt_card
end NSP14.Additive
