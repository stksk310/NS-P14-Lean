module
public import NSP14.Additive.ZeroSumSequence
public import NSP14.Additive.Sumset
@[expose] public section
open scoped Pointwise BigOperators
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {ℓ : ℕ}
/-- Subsets of positions are summed before any equal sums are identified. -/
def indexedSubsetSums (seq : Fin ℓ → G) (I : Finset (Fin ℓ)) : Finset G :=
  I.powerset.image (fun J => ∑ j ∈ J, seq j)
theorem mem_indexedSubsetSums (seq : Fin ℓ → G) (I : Finset (Fin ℓ)) (x : G) :
    x ∈ indexedSubsetSums seq I ↔ ∃ J ⊆ I, ∑ j ∈ J, seq j = x := by
  simp only [indexedSubsetSums, Finset.mem_image, Finset.mem_powerset]
@[simp] theorem zero_mem_indexedSubsetSums (seq : Fin ℓ → G) (I : Finset (Fin ℓ)) :
    0 ∈ indexedSubsetSums seq I :=
  (mem_indexedSubsetSums seq I 0).mpr ⟨∅,Finset.empty_subset _,by simp⟩
theorem total_mem_indexedSubsetSums (seq : Fin ℓ → G) (I : Finset (Fin ℓ)) :
    ∑ i ∈ I, seq i ∈ indexedSubsetSums seq I :=
  (mem_indexedSubsetSums seq I _).mpr ⟨I,Finset.Subset.refl _,rfl⟩
theorem indexedSubsetSums_mono (seq : Fin ℓ → G) {I J : Finset (Fin ℓ)}
    (h : I ⊆ J) : indexedSubsetSums seq I ⊆ indexedSubsetSums seq J := by
  rintro x hx
  obtain ⟨K,hK,rfl⟩ := (mem_indexedSubsetSums seq I x).mp hx
  exact (mem_indexedSubsetSums seq J _).mpr ⟨K,hK.trans h,rfl⟩
theorem indexedSubsetSums_insert (seq : Fin ℓ → G) (I : Finset (Fin ℓ))
    (i : Fin ℓ) (hi : i ∉ I) :
    indexedSubsetSums seq (insert i I) =
      indexedSubsetSums seq I ∪ (seq i +ᵥ indexedSubsetSums seq I) := by
  ext x
  simp only [indexedSubsetSums, Finset.powerset_insert, Finset.image_union,
    Finset.mem_union, Finset.mem_image, Finset.mem_powerset, Finset.mem_vadd_finset]
  constructor
  · rintro (h | ⟨J,⟨K,hK,rfl⟩,hx⟩)
    · exact Or.inl h
    · right
      refine ⟨∑ j ∈ K, seq j,⟨K,hK,rfl⟩,?_⟩
      rw [Finset.sum_insert (fun h => hi (hK h))] at hx
      exact hx
  · rintro (h | ⟨y,⟨K,hK,rfl⟩,hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨insert i K,⟨K,hK,rfl⟩,by
        rw [Finset.sum_insert (fun h => hi (hK h))]
        exact hx⟩

theorem ZeroSumFree.total_not_mem_previous {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    {I J : Finset (Fin ℓ)} (hIJ : I ⊂ J) :
    ∑ j ∈ J, seq j ∉ indexedSubsetSums seq I := by
  rintro hx
  obtain ⟨K,hK,hEq⟩ := (mem_indexedSubsetSums seq I _).mp hx
  exact h.sum_ne_sum_of_ssubset (hK.trans_ssubset hIJ) hEq

theorem ZeroSumFree.subsetSums_strict {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    {I J : Finset (Fin ℓ)} (hIJ : I ⊂ J) :
    indexedSubsetSums seq I ⊂ indexedSubsetSums seq J := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨indexedSubsetSums_mono seq hIJ.subset,?_⟩
  intro he
  exact h.total_not_mem_previous hIJ (he ▸ total_mem_indexedSubsetSums seq J)

theorem ZeroSumFree.card_subsetSums {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    (I : Finset (Fin ℓ)) : I.card+1 ≤ (indexedSubsetSums seq I).card := by
  induction I using Finset.induction_on with
  | empty => simp [indexedSubsetSums]
  | @insert i I hi ih =>
    have hh := Finset.card_lt_card (h.subsetSums_strict (Finset.ssubset_insert hi))
    rw [Finset.card_insert_of_notMem hi]
    omega

theorem ZeroSumFree.neg_not_mem_subsetSums {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    {I : Finset (Fin ℓ)} {i : Fin ℓ} (hi : i ∉ I) :
    -seq i ∉ indexedSubsetSums seq I := by
  rintro hx
  obtain ⟨J,hJ,hEq⟩ := (mem_indexedSubsetSums seq I _).mp hx
  apply h (insert i J) (Finset.insert_nonempty _ _)
  rw [Finset.sum_insert (fun h => hi (hJ h)), hEq, add_neg_cancel]
end NSP14.Additive
