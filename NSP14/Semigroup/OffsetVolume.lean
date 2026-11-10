module

public import NSP14.Semigroup.OffsetLevel
public import NSP14.Combinatorics.FiniteRank
public import NSP14.Ordinary.OffsetVolumeArithmetic

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- All proper prefixes precede the endpoint in least-offset order. -/
theorem leastOffsetLength_le_rank (r : Fin S.multiplicity) :
    S.leastOffsetLength r ≤ NSP14.lowerRank S.leastOffset r := by
  let w := S.leastOffsetWord r
  let f : Fin w.length → Fin S.multiplicity :=
    fun i => S.residue (S.offsetWordValue (w.take i.val))
  have hc : (Finset.univ : Finset (Fin w.length)).card ≤
      (NSP14.lowerRankSet S.leastOffset r).card := by
    apply Finset.card_le_card_of_injOn f
    · intro i _
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change S.leastOffset (S.residue (S.offsetWordValue (w.take i.val))) < S.leastOffset r
      rw [S.leastOffset_take]
      have hs := S.offsetWord_take_strict w i.isLt le_rfl
      rw [List.take_length, (S.leastOffsetWord_spec r).1] at hs
      exact hs
    · intro i _ j _ he
      have h := S.leastOffset_prefix_injective r
        (show (fun a : Fin (w.length + 1) =>
          S.residue (S.offsetWordValue (w.take a.val))) ⟨i.val, by have := i.isLt; omega⟩ =
          (fun a : Fin (w.length + 1) =>
            S.residue (S.offsetWordValue (w.take a.val))) ⟨j.val, by have := j.isLt; omega⟩ from he)
      exact Fin.ext (congrArg (fun q : Fin (w.length + 1) => q.val) h)
  simpa only [Finset.card_univ, Fintype.card_fin, w, (S.leastOffsetWord_spec r).2, NSP14.lowerRank] using hc

/-- The pointwise path bound (3.1), expressed without choosing a sorted list. -/
theorem offsetLevel_path_bound (r : Fin S.multiplicity) :
    S.offsetLevel r - 1 ≤ min S.deficit (NSP14.lowerRank S.leastOffset r - 1) := by
  have hd := S.offsetLevel_le_deficit_succ r
  have hl := S.offsetLevel_le_length r
  have hr := S.leastOffsetLength_le_rank r
  omega

/-- The sharp total offset budget. The zero residue contributes zero and is
removed only after the full finite permutation sum has been evaluated. -/
theorem offset_volume_bound :
    (∑ r ∈ (Finset.univ : Finset (Fin S.multiplicity)).filter (fun r => r.val ≠ 0),
      ((S.offsetLevel r - 1 : ℕ) : ℚ)) ≤
    (S.deficit : ℚ) * NSP14.Ordinary.SmallScalar.volume S.embeddingDimension S.deficit := by
  have hzero : (∑ r ∈ (Finset.univ : Finset (Fin S.multiplicity)).filter (fun r => r.val ≠ 0),
      ((S.offsetLevel r - 1 : ℕ) : ℚ)) =
      ∑ r : Fin S.multiplicity, ((S.offsetLevel r - 1 : ℕ) : ℚ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro r _ hn
    have hr : r.val = 0 := by
      by_contra h
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [S.offsetLevel_zero r hr]
    norm_num
  rw [hzero]
  have hsum : (∑ r : Fin S.multiplicity,
      ((min S.deficit (NSP14.lowerRank S.leastOffset r - 1) : ℕ) : ℚ)) =
      ∑ k ∈ Finset.range S.multiplicity, ((min S.deficit (k - 1) : ℕ) : ℚ) := by
    have he := (NSP14.lowerRankEquiv S.leastOffset_injective).sum_comp
      (fun i => ((min S.deficit (i.val - 1) : ℕ) : ℚ))
    simp only [NSP14.lowerRankEquiv_val] at he
    have he2 := Fin.sum_univ_eq_sum_range
      (fun k => ((min S.deficit (k - 1) : ℕ) : ℚ)) (Fintype.card (Fin S.multiplicity))
    simpa only [Fintype.card_fin] using he.trans he2
  calc
    _ ≤ ∑ r : Fin S.multiplicity,
        ((min S.deficit (NSP14.lowerRank S.leastOffset r - 1) : ℕ) : ℚ) := by
      apply Finset.sum_le_sum
      intro r _
      exact Nat.cast_le.mpr (S.offsetLevel_path_bound r)
    _ = _ := hsum
    _ = (S.deficit : ℚ) * NSP14.Ordinary.SmallScalar.volume S.embeddingDimension S.deficit := by
      have he := S.embeddingDimension_pos
      have hm : S.multiplicity = S.deficit + 1 + (S.embeddingDimension - 1) := by
        have := S.multiplicity_eq_embedding_add_deficit
        omega
      rw [hm, NSP14.Ordinary.min_staircase_sum]
      unfold NSP14.Ordinary.SmallScalar.volume
      rw [Nat.cast_sub (show 1 ≤ S.embeddingDimension by omega)]
      push_cast
      ring

end NSP14.NumericalSemigroup
