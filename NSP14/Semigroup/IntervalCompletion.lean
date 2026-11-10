module
public import NSP14.ArithmeticSequence.Interval
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NSP14.NumericalSemigroup)

noncomputable def maxAtom : ℕ := S.atoms.max' ⟨S.multiplicity,S.multiplicity_mem_atoms⟩

theorem multiplicity_le_maxAtom : S.multiplicity ≤ S.maxAtom :=
  Finset.le_max' _ _ S.multiplicity_mem_atoms

theorem atom_le_maxAtom {n : ℕ} (hn : n ∈ S.atoms) : n ≤ S.maxAtom :=
  Finset.le_max' _ _ hn

noncomputable def width : ℕ := S.maxAtom-S.multiplicity

theorem maxAtom_eq : S.maxAtom=S.multiplicity+S.width := by
  unfold width
  exact (Nat.add_sub_of_le S.multiplicity_le_maxAtom).symm

theorem width_pos (he : 2 ≤ S.embeddingDimension) : 1 ≤ S.width := by
  by_contra hn
  have hz : S.width=0 := by omega
  have heq : S.maxAtom=S.multiplicity := by rw [S.maxAtom_eq,hz,Nat.add_zero]
  have hs : S.atoms ⊆ {S.multiplicity} := by
    intro n hn
    have hu := S.atom_le_maxAtom hn
    have ha := (S.mem_atoms_iff _).mp hn
    have hl := S.multiplicity_le ha.1 ha.2.1
    simp only [Finset.mem_singleton]
    omega
  have hc := Finset.card_le_card hs
  have hc' : S.embeddingDimension ≤ 1 := by simpa only [embeddingDimension,Finset.card_singleton] using hc
  omega

noncomputable def intervalAP (he : 2 ≤ S.embeddingDimension) : NSP14.ArithmeticSequence.Data :=
  NSP14.ArithmeticSequence.intervalData S.multiplicity S.width
    (he.trans S.embeddingDimension_le_multiplicity) (S.width_pos he)

/-- The actual completion is the AP with the same literal generated interval.
Its conductor is a cofinite witness, not claimed to be the least conductor. -/
noncomputable def intervalCompletion (he : 2 ≤ S.embeddingDimension) : NSP14.NumericalSemigroup :=
  (S.intervalAP he).source

theorem intervalCompletion_carrier (he : 2 ≤ S.embeddingDimension) :
    (S.intervalCompletion he).carrier=AddSubmonoid.closure (Set.Icc S.multiplicity S.maxAtom) := by
  rw [S.maxAtom_eq]
  exact (NSP14.ArithmeticSequence.interval_closure S.multiplicity S.width
    (he.trans S.embeddingDimension_le_multiplicity) (S.width_pos he)).symm

theorem intervalCompletion_multiplicity (he : 2 ≤ S.embeddingDimension) :
    (S.intervalCompletion he).multiplicity=S.multiplicity := (S.intervalAP he).multiplicity

theorem intervalCompletion_embeddingDimension (he : 2 ≤ S.embeddingDimension) :
    (S.intervalCompletion he).embeddingDimension=min S.width (S.multiplicity-1)+1 :=
  (S.intervalAP he).embeddingDimension

theorem intervalCompletion_ordinary_rank (he : 2 ≤ S.embeddingDimension)
    (hw : S.multiplicity-1 ≤ S.width) :
    (S.intervalCompletion he).embeddingDimension=S.multiplicity := by
  rw [S.intervalCompletion_embeddingDimension he,min_eq_right hw]
  have := S.multiplicity_pos
  omega

theorem source_le_intervalCompletion (he : 2 ≤ S.embeddingDimension) :
    S.carrier ≤ (S.intervalCompletion he).carrier := by
  rw [← S.closure_atoms,S.intervalCompletion_carrier he]
  apply AddSubmonoid.closure_mono
  intro n hn
  have ha := (S.mem_atoms_iff _).mp hn
  exact ⟨S.multiplicity_le ha.1 ha.2.1,S.atom_le_maxAtom hn⟩

/-- The wide actual completion is literally the ordinary semigroup,
including zero; no Betti assertion is encoded by this identification. -/
theorem intervalCompletion_ordinary_mem (he : 2 ≤ S.embeddingDimension)
    (hw : S.multiplicity-1 ≤ S.width) (x : ℕ) :
    x ∈ S.intervalCompletion he ↔ x=0 ∨ S.multiplicity ≤ x := by
  constructor
  · intro hx
    by_cases hz : x=0
    · exact Or.inl hz
    · have h := (S.intervalCompletion he).multiplicity_le hx (by omega)
      rw [S.intervalCompletion_multiplicity he] at h
      exact Or.inr h
  · rintro (rfl|hx)
    · exact (S.intervalCompletion he).zero_mem
    change ∃ l j, j ≤ min S.width (S.multiplicity-1)*l ∧ x=l*S.multiplicity+j*1
    have hm := S.multiplicity_pos
    have hl : 1 ≤ x/S.multiplicity := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hx)
    have hj : x%S.multiplicity ≤ S.multiplicity-1 := by have := Nat.mod_lt x hm;omega
    refine ⟨x/S.multiplicity,x%S.multiplicity,?_,?_⟩
    · rw [min_eq_right hw]
      exact hj.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S.multiplicity-1) hl)
    · have h := Nat.mod_add_div x S.multiplicity
      nlinarith
end NSP14.NumericalSemigroup
