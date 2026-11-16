module
public import NSP14.Additive.IndexedSubsetSums
public import Mathlib.Tactic.Abel
@[expose] public section
open scoped Pointwise BigOperators
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {ℓ : ℕ}
/-- A new position increases the number of positional subset sums by exactly one. -/
def Sharp (seq : Fin ℓ → G) (I : Finset (Fin ℓ)) (i : Fin ℓ) : Prop :=
  (indexedSubsetSums seq (insert i I)).card = (indexedSubsetSums seq I).card+1

/-- One new element under a translation, with 0 lost, forces backward closure
at every nonzero point. No coset decomposition is needed. -/
theorem erase_zero_subset_translate (S : Finset G) (b : G) (h0 : 0 ∈ S)
    (hz : 0 ∉ b +ᵥ S) (hc : (S ∪ (b +ᵥ S)).card = S.card+1) :
    S.erase 0 ⊆ b +ᵥ S := by
  have hcard := Finset.card_vadd_finset b S
  have hu := Finset.card_union_add_card_inter S (b +ᵥ S)
  have hd := Finset.card_sdiff_add_card_inter S (b +ᵥ S)
  have hOne : (S \ (b +ᵥ S)).card = 1 := by omega
  have hsub : ({0} : Finset G) ⊆ S \ (b +ᵥ S) := by
    simpa only [Finset.singleton_subset_iff, Finset.mem_sdiff] using And.intro h0 hz
  have he : S \ (b +ᵥ S) = {0} :=
    (Finset.eq_of_subset_of_card_le hsub (by simp [hOne])).symm
  intro x hx
  by_contra hn
  have hm : x ∈ S \ (b +ᵥ S) := Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hx).2,hn⟩
  rw [he,Finset.mem_singleton] at hm
  exact (Finset.mem_erase.mp hx).1 hm

theorem Sharp.sumset_eq {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    {I : Finset (Fin ℓ)} {i : Fin ℓ} (hi : i ∉ I) (hs : Sharp seq I i) :
    indexedSubsetSums seq (insert i I) =
      insert (∑ j ∈ insert i I, seq j) (indexedSubsetSums seq I) := by
  symm
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · exact Finset.insert_subset_iff.mpr ⟨total_mem_indexedSubsetSums _ _,
      indexedSubsetSums_mono seq (Finset.subset_insert _ _)⟩
  · rw [Finset.card_insert_of_notMem
      (h.total_not_mem_previous (Finset.ssubset_insert hi))]
    exact (show _ = _ from hs).le

theorem Sharp.term_mem {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    {I : Finset (Fin ℓ)} (hI : I.Nonempty) {i : Fin ℓ} (hi : i ∉ I)
    (hs : Sharp seq I i) : seq i ∈ indexedSubsetSums seq I := by
  have hm : seq i ∈ indexedSubsetSums seq (insert i I) :=
    (mem_indexedSubsetSums _ _ _).mpr ⟨{i},by simp,by simp⟩
  rw [hs.sumset_eq h hi,Finset.mem_insert] at hm
  rcases hm with hm | hm
  · rw [Finset.sum_insert hi] at hm
    have he : ∑ j ∈ I, seq j = 0 := by
      exact add_left_cancel (hm.symm.trans (add_zero _).symm)
    exact False.elim (h I hI he)
  · exact hm

theorem Sharp.backward {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    {I : Finset (Fin ℓ)} {i : Fin ℓ} (hi : i ∉ I) (hs : Sharp seq I i)
    {x : G} (hx : x ∈ indexedSubsetSums seq I) (hx0 : x ≠ 0) :
    x-seq i ∈ indexedSubsetSums seq I := by
  have hz : 0 ∉ seq i +ᵥ indexedSubsetSums seq I := by
    intro hh
    obtain ⟨y,hy,he⟩ := Finset.mem_vadd_finset.mp hh
    have he' : y = -seq i := eq_neg_iff_add_eq_zero.mpr
      (by simpa only [vadd_eq_add, add_comm] using he)
    exact h.neg_not_mem_subsetSums hi (he' ▸ hy)
  have hc : (indexedSubsetSums seq I ∪ (seq i +ᵥ indexedSubsetSums seq I)).card =
      (indexedSubsetSums seq I).card+1 := by
    rw [←indexedSubsetSums_insert seq I i hi]
    exact hs
  have hh := erase_zero_subset_translate _ (seq i) (zero_mem_indexedSubsetSums _ _) hz hc
    (Finset.mem_erase.mpr ⟨hx0,hx⟩)
  obtain ⟨y,hy,he⟩ := Finset.mem_vadd_finset.mp hh
  have he' : y = x-seq i := by
    change seq i+y=x at he
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using he)
  exact he' ▸ hy

/-- Savchev–Chen Proposition 2(c), proved directly by two backward steps. -/
theorem sharp_term_unique {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    {I : Finset (Fin ℓ)} (hI : I.Nonempty) {i j : Fin ℓ}
    (hi : i ∉ I) (hj : j ∉ I) (hsi : Sharp seq I i) (hsj : Sharp seq I j) :
    seq i = seq j := by
  by_contra hn
  have hjS := hsj.term_mem h hI hj
  have hdiff := hsi.backward h hi hjS (h.term_ne_zero j)
  have hd0 : seq j-seq i ≠ 0 := sub_ne_zero.mpr (Ne.symm hn)
  have hneg := hsj.backward h hj hdiff hd0
  have he : seq j-seq i-seq j = -seq i := by abel
  rw [he] at hneg
  exact h.neg_not_mem_subsetSums hi hneg

/-- A second occurrence of the same term preserves sharpness, with all
positions retained. -/
theorem Sharp.insert_equal {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    {I : Finset (Fin ℓ)} {i j : Fin ℓ} (hi : i ∉ I) (hj : j ∉ I)
    (hij : i ≠ j) (heq : seq j = seq i) (hs : Sharp seq I i) :
    Sharp seq (insert j I) i := by
  have hii : i ∉ insert j I := by simp [hij,hi]
  have hsets : indexedSubsetSums seq (insert j I) = indexedSubsetSums seq (insert i I) := by
    rw [indexedSubsetSums_insert seq I j hj,indexedSubsetSums_insert seq I i hi,heq]
  have hsj : Sharp seq I j := by unfold Sharp; rw [hsets]; exact hs
  let S := indexedSubsetSums seq I
  let S' := indexedSubsetSums seq (insert j I)
  let t := ∑ k ∈ insert j I, seq k
  have he : S' = insert t S := hsj.sumset_eq h hj
  have hsub : seq i +ᵥ S ⊆ S' := by
    dsimp only [S,S']
    rw [indexedSubsetSums_insert seq I j hj,heq]
    exact Finset.subset_union_right
  have hnext : indexedSubsetSums seq (insert i (insert j I)) = insert (seq i+t) S' := by
    calc
      _ = S' ∪ (seq i +ᵥ S') := indexedSubsetSums_insert seq _ i hii
      _ = S' ∪ (seq i +ᵥ insert t S) := congrArg (fun T => S' ∪ (seq i +ᵥ T)) he
      _ = insert (seq i+t) S' := by
        rw [Finset.vadd_finset_insert,Finset.union_insert,Finset.union_eq_left.mpr hsub]
        rfl
  have hn : seq i+t ∉ S' := by
    have hh := h.total_not_mem_previous (Finset.ssubset_insert hii)
    rw [Finset.sum_insert hii] at hh
    exact hh
  unfold Sharp
  rw [hnext,Finset.card_insert_of_notMem hn]

theorem Sharp.persist_equal {seq : Fin ℓ → G} (h : ZeroSumFree seq)
    {I J : Finset (Fin ℓ)} {i : Fin ℓ} (hi : i ∉ I) (hiJ : i ∉ J)
    (hval : ∀ j ∈ J, seq j = seq i) (hs : Sharp seq I i) :
    Sharp seq (I ∪ J) i := by
  induction J using Finset.induction_on with
  | empty => simpa only [Finset.union_empty] using hs
  | @insert j J hj ih =>
    have hij : i ≠ j := by intro he; subst j; simp at hiJ
    have hiJ' : i ∉ J := fun hh => hiJ (Finset.mem_insert_of_mem hh)
    have hval' : ∀ k ∈ J, seq k = seq i := fun k hk => hval k (Finset.mem_insert_of_mem hk)
    have hh := ih hiJ' hval'
    by_cases hjI : j ∈ I
    · have he : I ∪ insert j J = I ∪ J := by ext k; simp only [Finset.mem_union,Finset.mem_insert]; aesop
      rw [he]; exact hh
    · rw [Finset.union_insert]
      exact hh.insert_equal h (by simp [hi,hiJ']) (by simp [hjI,hj]) hij
        (hval j (Finset.mem_insert_self _ _))
end NSP14.Additive
