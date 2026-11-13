module
public import NSP14.Additive.SharpSequence
@[expose] public section
open scoped Pointwise BigOperators
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {ℓ : ℕ}

/-- The suffix-rearrangement lemma, expressed without choosing an ordering.
The final position lies outside the prescribed initial positions. -/
theorem exists_sharp_terminal {seq : Fin ℓ → G} (hz : ZeroSumFree seq)
    (U I₀ : Finset (Fin ℓ)) (hI₀ : I₀ ⊆ U) (hI₀ne : I₀.Nonempty)
    (hlarge : 2*I₀.card ≤ (indexedSubsetSums seq I₀).card)
    (hsmall : (indexedSubsetSums seq U).card < 2*U.card) :
    ∃ j ∈ U \ I₀, Sharp seq (U.erase j) j := by
  let candidates := U.powerset.filter (fun I => I₀ ⊆ I ∧
    2*I.card ≤ (indexedSubsetSums seq I).card)
  have hc : I₀ ∈ candidates := by simp only [candidates,Finset.mem_filter,Finset.mem_powerset]; exact ⟨hI₀,Finset.Subset.refl _,hlarge⟩
  obtain ⟨I,hI,hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨I₀,hc⟩
  obtain ⟨hIU,hI₀I,hIlarge⟩ := (Finset.mem_filter.mp hI)
  have hIU' : I ⊆ U := Finset.mem_powerset.mp hIU
  have hIne : I.Nonempty := hI₀ne.mono hI₀I
  have hproper : ¬ U ⊆ I := by
    intro he
    have heq := hIU'.antisymm he
    rw [heq] at hIlarge
    omega
  have hsharp (j : Fin ℓ) (hj : j ∈ U \ I) : Sharp seq I j := by
    obtain ⟨hjU,hjI⟩ := Finset.mem_sdiff.mp hj
    have hsub : insert j I ⊆ U := Finset.insert_subset_iff.mpr ⟨hjU,hIU'⟩
    have hfail : ¬2*(insert j I).card ≤ (indexedSubsetSums seq (insert j I)).card := by
      intro hh
      have hm : insert j I ∈ candidates := by
        simp only [candidates,Finset.mem_filter,Finset.mem_powerset]
        exact ⟨hsub,hI₀I.trans (Finset.subset_insert _ _),hh⟩
      have he := hmax _ hm
      rw [Finset.card_insert_of_notMem hjI] at he
      omega
    have hg := Finset.card_lt_card (hz.subsetSums_strict (Finset.ssubset_insert hjI))
    rw [Finset.card_insert_of_notMem hjI] at hfail
    unfold Sharp
    omega
  obtain ⟨j,hj⟩ := Finset.sdiff_nonempty.mpr hproper
  have hjI := (Finset.mem_sdiff.mp hj).2
  have hjU := (Finset.mem_sdiff.mp hj).1
  refine ⟨j,Finset.mem_sdiff.mpr ⟨hjU,fun hh => hjI (hI₀I hh)⟩,?_⟩
  have hIE : I ⊆ U.erase j := by
    intro k hk
    exact Finset.mem_erase.mpr ⟨fun he => hjI (he ▸ hk),hIU' hk⟩
  have hp := (hsharp j hj).persist_equal hz hjI
    (J := U.erase j \ I) (by simp) ?_
  · rw [Finset.union_sdiff_of_subset hIE] at hp
    exact hp
  · intro k hk
    have hkU := Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hk).1
    have hkI := (Finset.mem_sdiff.mp hk).2
    exact sharp_term_unique hz hIne hkI hjI
      (hsharp k (Finset.mem_sdiff.mpr ⟨hkU,hkI⟩)) (hsharp j hj)

theorem Sharp.prefix_sumset {seq : Fin ℓ → G} (hz : ZeroSumFree seq)
    {U : Finset (Fin ℓ)} {i : Fin ℓ} (hi : i ∈ U) (hs : Sharp seq (U.erase i) i) :
    indexedSubsetSums seq (U.erase i) =
      (indexedSubsetSums seq U).erase (∑ j ∈ U, seq j) := by
  have he := hs.sumset_eq hz (Finset.notMem_erase i U)
  rw [Finset.insert_erase hi] at he
  rw [he,Finset.erase_insert (hz.total_not_mem_previous (Finset.erase_ssubset hi))]

/-- The last value of a sharp ordering is invariant under rearranging all
positions. This is Lev Claim 3, derived from the same backward-closure proof. -/
theorem sharp_terminal_unique {seq : Fin ℓ → G} (hz : ZeroSumFree seq)
    {U : Finset (Fin ℓ)} (hU : 2 ≤ U.card) {i j : Fin ℓ} (hi : i ∈ U) (hj : j ∈ U)
    (hsi : Sharp seq (U.erase i) i) (hsj : Sharp seq (U.erase j) j) :
    seq i = seq j := by
  have hsame : indexedSubsetSums seq (U.erase i) = indexedSubsetSums seq (U.erase j) :=
    (hsi.prefix_sumset hz hi).trans (hsj.prefix_sumset hz hj).symm
  have hJ : (U.erase j).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hj]; omega)
  by_contra hn
  have hc := hsj.term_mem hz hJ (Finset.notMem_erase j U)
  rw [←hsame] at hc
  have hd := hsi.backward hz (Finset.notMem_erase i U) hc (hz.term_ne_zero j)
  rw [hsame] at hd
  have hneg := hsj.backward hz (Finset.notMem_erase j U) hd
    (sub_ne_zero.mpr (Ne.symm hn))
  have he : seq j-seq i-seq j = -seq i := by abel
  rw [he,←hsame] at hneg
  exact hz.neg_not_mem_subsetSums (Finset.notMem_erase i U) hneg
end NSP14.Additive
