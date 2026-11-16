module
public import NSP14.Additive.SharpRearrangement
@[expose] public section
open scoped Pointwise BigOperators Classical
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G] {ℓ : ℕ}

/-- A positional set admits an ordering in which each later value is a
difference of two earlier subset sums. The ordering is represented by a derivation. -/
inductive Connected (seq : Fin ℓ → G) : Finset (Fin ℓ) → Prop
  | singleton (i : Fin ℓ) : Connected seq {i}
  | insert {I : Finset (Fin ℓ)} {i : Fin ℓ} (hi : i ∉ I) (hI : Connected seq I)
      (hvalue : seq i ∈ indexedSubsetSums seq I - indexedSubsetSums seq I) :
      Connected seq (insert i I)

theorem Connected.nonempty {seq : Fin ℓ → G} {I : Finset (Fin ℓ)}
    (hc : Connected seq I) : I.Nonempty := by
  cases hc with
  | singleton i => exact Finset.singleton_nonempty i
  | insert => exact Finset.insert_nonempty _ _

theorem connected_constant (seq : Fin ℓ → G) (I : Finset (Fin ℓ)) (hI : I.Nonempty)
    (c : G) (he : ∀ i ∈ I, seq i = c) : Connected seq I := by
  induction I using Finset.induction_on with
  | empty => exact False.elim (Finset.not_nonempty_empty hI)
  | @insert i I hi ih =>
    obtain rfl | hI' := I.eq_empty_or_nonempty
    · exact Connected.singleton i
    · apply Connected.insert hi (ih hI' (fun j hj => he j (Finset.mem_insert_of_mem hj)))
      obtain ⟨j,hj⟩ := hI'
      have hv : seq i = seq j := (he i (Finset.mem_insert_self _ _)).trans
        (he j (Finset.mem_insert_of_mem hj)).symm
      exact Finset.mem_sub.mpr ⟨seq j,
        (mem_indexedSubsetSums _ _ _).mpr ⟨{j},by simpa using hj,by simp⟩,
        0,zero_mem_indexedSubsetSums _ _,by simp [hv]⟩

theorem disjoint_translate_of_not_mem_sub (S : Finset G) (c : G) (hc : c ∉ S-S) :
    Disjoint S (c +ᵥ S) := by
  rw [Finset.disjoint_left]
  intro x hx hcx
  obtain ⟨y,hy,he⟩ := Finset.mem_vadd_finset.mp hcx
  apply hc
  exact Finset.mem_sub.mpr ⟨x,hx,y,hy,by rw [←he]; simp⟩

/-- A maximal connected initial set either covers U or forces a sharp
terminal outside that initial set. -/
theorem connected_or_sharp_outside {seq : Fin ℓ → G} (hz : ZeroSumFree seq)
    (U I₀ : Finset (Fin ℓ)) (hI₀ : I₀ ⊆ U) (hconn : Connected seq I₀)
    (hsmall : (indexedSubsetSums seq U).card < 2*U.card) :
    Connected seq U ∨ ∃ j ∈ U \ I₀, Sharp seq (U.erase j) j := by
  let candidates := U.powerset.filter (fun I => I₀ ⊆ I ∧ Connected seq I)
  have hc : I₀ ∈ candidates := by
    simp only [candidates,Finset.mem_filter,Finset.mem_powerset]
    exact ⟨hI₀,Finset.Subset.refl _,hconn⟩
  obtain ⟨I,hI,hmax⟩ := Finset.exists_max_image candidates Finset.card ⟨I₀,hc⟩
  obtain ⟨hIU,hI₀I,hIconn⟩ := Finset.mem_filter.mp hI
  have hIU' : I ⊆ U := Finset.mem_powerset.mp hIU
  by_cases he : I = U
  · exact Or.inl (he ▸ hIconn)
  · right
    have hproper : ¬ U ⊆ I := fun h => he (hIU'.antisymm h)
    obtain ⟨j,hjU,hjI⟩ := Finset.not_subset.mp hproper
    have hnot : seq j ∉ indexedSubsetSums seq I - indexedSubsetSums seq I := by
      intro hm
      have hm' : insert j I ∈ candidates := by
        simp only [candidates,Finset.mem_filter,Finset.mem_powerset]
        exact ⟨Finset.insert_subset_iff.mpr ⟨hjU,hIU'⟩,
          hI₀I.trans (Finset.subset_insert _ _),Connected.insert hjI hIconn hm⟩
      have hh := hmax _ hm'
      rw [Finset.card_insert_of_notMem hjI] at hh
      omega
    have hdis := disjoint_translate_of_not_mem_sub (indexedSubsetSums seq I) (seq j) hnot
    have hcard : (indexedSubsetSums seq (insert j I)).card =
        2*(indexedSubsetSums seq I).card := by
      rw [indexedSubsetSums_insert _ _ _ hjI,Finset.card_union_of_disjoint hdis,
        Finset.card_vadd_finset,two_mul]
    have hlarge : 2*(insert j I).card ≤ (indexedSubsetSums seq (insert j I)).card := by
      rw [hcard,Finset.card_insert_of_notMem hjI]
      have hh := hz.card_subsetSums I
      omega
    obtain ⟨k,hk,hs⟩ := exists_sharp_terminal hz U (insert j I)
      (Finset.insert_subset_iff.mpr ⟨hjU,hIU'⟩) (Finset.insert_nonempty _ _) hlarge hsmall
    refine ⟨k,Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hk).1,?_⟩,hs⟩
    intro hh
    exact (Finset.mem_sdiff.mp hk).2 (Finset.mem_insert_of_mem (hI₀I hh))

/-- The structural core of Savchev–Chen, in Lev's few-subset-sums form.
All multiplicities remain attached to their original positions. -/
theorem connected_of_few_subsetSums {seq : Fin ℓ → G} (hz : ZeroSumFree seq)
    (U : Finset (Fin ℓ)) (hsmall : (indexedSubsetSums seq U).card < 2*U.card) :
    Connected seq U := by
  have hU : 2 ≤ U.card := by have hh := hz.card_subsetSums U; omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (by omega : 0 < U.card)
  rcases connected_or_sharp_outside hz U {i} (by simpa using hi)
      (Connected.singleton i) hsmall with hc | ⟨j,hj,hsj⟩
  · exact hc
  have hjU := (Finset.mem_sdiff.mp hj).1
  let C := U.filter (fun k => seq k = seq j)
  have hjC : j ∈ C := by simp [C,hjU]
  have hCne : C.Nonempty := ⟨j,hjC⟩
  have hCU : C ⊆ U := Finset.filter_subset _ _
  have hCconn : Connected seq C := connected_constant seq C hCne (seq j)
    (fun k hk => (Finset.mem_filter.mp hk).2)
  rcases connected_or_sharp_outside hz U C hCU hCconn hsmall with hc | ⟨k,hk,hsk⟩
  · exact hc
  have hkU := (Finset.mem_sdiff.mp hk).1
  have he := sharp_terminal_unique hz hU hkU hjU hsk hsj
  exact False.elim ((Finset.mem_sdiff.mp hk).2 (by simp [C,hkU,he]))
end NSP14.Additive
