module

public import NSP14.Semigroup.Order

@[expose] public section

open scoped BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

noncomputable def degreeSet (n : ℕ) : Finset ℕ := by
  classical
  exact S.aperySet.filter (fun x => S.order x = n)

theorem degree_zero : S.degreeSet 0 = {0} := by
  classical
  ext x
  simp only [degreeSet, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hord⟩
    exact (S.order_eq_zero_iff ((S.mem_aperySet_iff _).mp hx).1).mp hord
  · rintro rfl
    exact ⟨S.zero_mem_apery, S.order_zero⟩

theorem degree_one : S.degreeSet 1 = S.atoms.erase S.multiplicity := by
  classical
  ext x
  simp only [degreeSet, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨hx, hord⟩
    have ha := (S.order_one_iff_atom ((S.mem_aperySet_iff _).mp hx).1).mp hord
    refine ⟨?_, (S.mem_atoms_iff _).mpr ha⟩
    intro heq
    subst x
    exact S.multiplicity_not_apery hx
  · rintro ⟨hm, ha⟩
    have hatom := (S.mem_atoms_iff _).mp ha
    exact ⟨S.atom_apery hatom hm, S.atom_order hatom⟩

theorem degree_zero_card : (S.degreeSet 0).card = 1 := by rw [S.degree_zero]; simp
theorem degree_one_card : (S.degreeSet 1).card = S.embeddingDimension - 1 := by
  rw [S.degree_one, S.nonmultiplicity_atoms_card]

noncomputable def lowSet : Finset ℕ := insert 0 (S.atoms.erase S.multiplicity)
noncomputable def highSet : Finset ℕ := by
  classical
  exact S.aperySet.filter (fun x => 2 ≤ S.order x)

theorem lowSet_subset : S.lowSet ⊆ S.aperySet := by
  intro x hx
  rcases Finset.mem_insert.mp hx with h0 | ha
  · subst x; exact S.zero_mem_apery
  · exact S.nonmultiplicity_atoms_apery ha

theorem lowSet_card : S.lowSet.card = S.embeddingDimension := by
  have hz : 0 ∉ S.atoms.erase S.multiplicity := by
    intro h
    have ha := (S.mem_atoms_iff 0).mp (Finset.mem_erase.mp h).2
    have := ha.2.1
    omega
  unfold lowSet
  rw [Finset.card_insert_of_notMem hz, S.nonmultiplicity_atoms_card]
  have := S.embeddingDimension_pos
  omega

theorem highSet_eq_sdiff : S.highSet = S.aperySet \ S.lowSet := by
  classical
  ext x
  simp only [highSet, lowSet, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨hx, horder⟩
    refine ⟨hx, ?_⟩
    rintro (h0 | ha)
    · subst x; have := S.order_zero; omega
    · have hatom := (S.mem_atoms_iff _).mp (Finset.mem_erase.mp ha).2
      have := S.atom_order hatom
      omega
  · rintro ⟨hx, hn⟩
    refine ⟨hx, ?_⟩
    by_contra hlt
    have hsmall : S.order x = 0 ∨ S.order x = 1 := by omega
    rcases hsmall with h0 | h1
    · exact hn (Or.inl ((S.order_eq_zero_iff ((S.mem_aperySet_iff _).mp hx).1).mp h0))
    · have hmem : x ∈ S.degreeSet 1 := Finset.mem_filter.mpr ⟨hx, h1⟩
      rw [S.degree_one] at hmem
      exact hn (Or.inr hmem)

noncomputable def deficit : ℕ := S.multiplicity - S.embeddingDimension

/-- The numerical Apéry coordinates of degree >=2 have exactly the actual deficit. -/
theorem highSet_card : S.highSet.card = S.deficit := by
  rw [S.highSet_eq_sdiff, Finset.card_sdiff_of_subset S.lowSet_subset, S.apery_card, S.lowSet_card]
  rfl

theorem degree_two_le_deficit : (S.degreeSet 2).card ≤ S.deficit := by
  have hsub : S.degreeSet 2 ⊆ S.highSet := by
    intro x hx
    obtain ⟨ha, ho⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨ha, by omega⟩
  exact (Finset.card_le_card hsub).trans_eq S.highSet_card

theorem multiplicity_eq_embedding_add_deficit : S.multiplicity = S.embeddingDimension + S.deficit := by
  unfold deficit
  have := S.embeddingDimension_le_multiplicity
  omega

theorem apery_summands {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x + y ∈ S.aperySet) :
    x ∈ S.aperySet ∧ y ∈ S.aperySet := by
  constructor
  · apply (S.mem_apery_iff_no_predecessor hx).mpr
    rintro ⟨p, hp, heq⟩
    exact S.apery_no_predecessor hxy ⟨p + y, S.add_mem hp hy, by omega⟩
  · apply (S.mem_apery_iff_no_predecessor hy).mpr
    rintro ⟨p, hp, heq⟩
    exact S.apery_no_predecessor hxy ⟨x + p, S.add_mem hx hp, by omega⟩

/-- Removing one atom from a longest Apéry representation lowers its order by exactly one. -/
theorem apery_predecessor_order {w k : ℕ} (hw : w ∈ S.aperySet) (hk : S.order w = k + 1) :
    ∃ v ∈ S.aperySet, S.order v = k := by
  have hwS := ((S.mem_aperySet_iff _).mp hw).1
  have hex := S.order_realized_by_atoms hwS
  rw [hk] at hex
  obtain ⟨f, hf, hsum⟩ := hex
  let v := ∑ i : Fin k, f i.succ
  have hvmem : v ∈ S := S.sum_mem _ _ (fun i _ => (hf i.succ).1)
  have heq : w = f 0 + v := by simpa [v, Fin.sum_univ_succ] using hsum.symm
  have hvap : v ∈ S.aperySet := (S.apery_summands (hf 0).1 hvmem (by rwa [← heq])).2
  have hlen : k ≤ S.order v := S.atomic_length_le (fun i : Fin k => f i.succ)
    (fun i => hf i.succ) rfl
  have hadd := S.order_add (hf 0).1 hvmem
  rw [← heq, hk, S.atom_order (hf 0)] at hadd
  exact ⟨v, hvap, by omega⟩

theorem degree_exists_le {w : ℕ} (hw : w ∈ S.aperySet) (n : ℕ) (hn : n ≤ S.order w) :
    ∃ v ∈ S.aperySet, S.order v = n := by
  suffices h : ∀ k, ∀ w ∈ S.aperySet, S.order w = k → n ≤ k →
      ∃ v ∈ S.aperySet, S.order v = n from h (S.order w) w hw rfl hn
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro w hw heq hn
    by_cases hnk : n = k
    · exact ⟨w, hw, heq.trans hnk.symm⟩
    have hpos : 0 < k := by omega
    obtain ⟨v, hv, ho⟩ := S.apery_predecessor_order hw
      (show S.order w = (k - 1) + 1 by omega)
    exact ih (k - 1) (by omega) v hv ho (by omega)

/-- The paper's ν≤δ+1 bound, already at the actual numerical-coordinate level. -/
theorem apery_order_bound {w : ℕ} (hw : w ∈ S.aperySet) : S.order w ≤ S.deficit + 1 := by
  classical
  let f : Fin (S.order w - 1) → ℕ := fun i =>
    Classical.choose (S.degree_exists_le hw (i.val + 2) (by have := i.isLt; omega))
  have hf : ∀ i, f i ∈ S.aperySet ∧ S.order (f i) = i.val + 2 := by
    intro i
    exact Classical.choose_spec (S.degree_exists_le hw (i.val + 2) (by have := i.isLt; omega))
  have hcard : (Finset.univ : Finset (Fin (S.order w - 1))).card ≤ S.highSet.card := by
    apply Finset.card_le_card_of_injOn f
    · intro i _
      exact Finset.mem_filter.mpr ⟨(hf i).1, by have := (hf i).2; omega⟩
    · intro i _ j _ heq
      apply Fin.ext
      have h := congrArg S.order heq
      rw [(hf i).2, (hf j).2] at h
      omega
  rw [Finset.card_univ, Fintype.card_fin, S.highSet_card] at hcard
  omega

end NSP14.NumericalSemigroup
