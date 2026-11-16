module

public import NSP14.Semigroup.Apery

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- Positive indecomposable elements of the actual additive submonoid. -/
def IsAtom (x : ℕ) : Prop :=
  x ∈ S ∧ 0 < x ∧ ∀ u ∈ S, ∀ v ∈ S, x = u + v → u = 0 ∨ v = 0

theorem multiplicity_atom : S.IsAtom S.multiplicity := by
  refine ⟨S.multiplicity_mem, S.multiplicity_pos, ?_⟩
  intro u hu v hv hsum
  by_cases h0 : u = 0
  · exact Or.inl h0
  have hm := S.multiplicity_le hu (by omega)
  exact Or.inr (by omega)

theorem atom_apery {x : ℕ} (hx : S.IsAtom x) (hm : x ≠ S.multiplicity) : x ∈ S.aperySet := by
  apply (S.mem_apery_iff_no_predecessor hx.1).mpr
  rintro ⟨y, hy, heq⟩
  rcases hx.2.2 y hy S.multiplicity S.multiplicity_mem heq with h0 | h0
  · apply hm; omega
  · have := S.multiplicity_pos; omega

/-- All atoms are finite: m and the indecomposable Apéry elements. -/
noncomputable def atoms : Finset ℕ := by
  classical
  exact insert S.multiplicity (S.aperySet.filter S.IsAtom)

theorem mem_atoms_iff (x : ℕ) : x ∈ S.atoms ↔ S.IsAtom x := by
  classical
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · rw [h]; exact S.multiplicity_atom
    · exact (Finset.mem_filter.mp h).2
  · intro hx
    by_cases hm : x = S.multiplicity
    · exact Finset.mem_insert.mpr (Or.inl hm)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr ⟨S.atom_apery hx hm, hx⟩))

theorem multiplicity_mem_atoms : S.multiplicity ∈ S.atoms :=
  (S.mem_atoms_iff _).mpr S.multiplicity_atom

theorem atoms_mem {x : ℕ} (hx : x ∈ S.atoms) : x ∈ S := ((S.mem_atoms_iff _).mp hx).1

theorem mem_closure_atoms {x : ℕ} (hx : x ∈ S) :
    x ∈ AddSubmonoid.closure (S.atoms : Set ℕ) := by
  classical
  suffices h : ∀ x, x ∈ S → x ∈ AddSubmonoid.closure (S.atoms : Set ℕ) from h x hx
  intro x
  induction x using Nat.strong_induction_on with
  | ind x ih =>
    intro hx
    by_cases h0 : x = 0
    · subst x; exact (AddSubmonoid.closure _).zero_mem
    by_cases ha : S.IsAtom x
    · exact AddSubmonoid.subset_closure ((S.mem_atoms_iff _).mpr ha)
    have hbad : ¬∀ u ∈ S, ∀ v ∈ S, x = u + v → u = 0 ∨ v = 0 := by
      intro h
      exact ha ⟨hx, by omega, h⟩
    push Not at hbad
    obtain ⟨u, hu, v, hv, heq, hune, hvne⟩ := hbad
    rw [heq]
    exact (AddSubmonoid.closure _).add_mem (ih u (by omega) hu) (ih v (by omega) hv)

theorem closure_atoms : AddSubmonoid.closure (S.atoms : Set ℕ) = S.carrier := by
  apply le_antisymm
  · apply AddSubmonoid.closure_le.mpr
    intro x hx
    exact S.atoms_mem hx
  · intro x hx
    exact S.mem_closure_atoms hx

/-- Every generating set contains every atom; this is actual minimality. -/
theorem atom_mem_of_generates {G : Set ℕ} (hG : AddSubmonoid.closure G = S.carrier)
    {a : ℕ} (ha : S.IsAtom a) : a ∈ G := by
  have hmem : a ∈ AddSubmonoid.closure G := by rw [hG]; exact ha.1
  refine AddSubmonoid.closure_induction (motive := fun x _ => x = a → a ∈ G) ?_ ?_ ?_ hmem rfl
  · intro x hx hxa
    simpa [hxa] using hx
  · intro heq
    have := ha.2.1
    omega
  · intro x y hx hy ihx ihy hsum
    have hxS : x ∈ S := by change x ∈ S.carrier; rw [← hG]; exact hx
    have hyS : y ∈ S := by change y ∈ S.carrier; rw [← hG]; exact hy
    rcases ha.2.2 x hxS y hyS hsum.symm with hx0 | hy0
    · exact ihy (by omega)
    · exact ihx (by omega)

noncomputable def embeddingDimension : ℕ := S.atoms.card

theorem embeddingDimension_pos : 0 < S.embeddingDimension := by
  unfold embeddingDimension
  exact Finset.card_pos.mpr ⟨_, S.multiplicity_mem_atoms⟩

theorem embeddingDimension_le_multiplicity : S.embeddingDimension ≤ S.multiplicity := by
  classical
  have hsub : S.atoms ⊆ insert S.multiplicity (S.aperySet.erase 0) := by
    intro x hx
    have ha := (S.mem_atoms_iff x).mp hx
    by_cases hm : x = S.multiplicity
    · exact Finset.mem_insert.mpr (Or.inl hm)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨by have := ha.2.1; omega, S.atom_apery ha hm⟩))
  have hm : S.multiplicity ∉ S.aperySet.erase 0 := by
    intro h
    exact S.multiplicity_not_apery (Finset.mem_erase.mp h).2
  have hcard : (insert S.multiplicity (S.aperySet.erase 0)).card = S.multiplicity := by
    rw [Finset.card_insert_of_notMem hm, Finset.card_erase_of_mem S.zero_mem_apery, S.apery_card]
    have := S.multiplicity_pos
    omega
  exact (Finset.card_le_card hsub).trans_eq hcard

theorem nonmultiplicity_atoms_card : (S.atoms.erase S.multiplicity).card = S.embeddingDimension - 1 := by
  classical
  rw [Finset.card_erase_of_mem S.multiplicity_mem_atoms]
  rfl

theorem nonmultiplicity_atoms_apery : S.atoms.erase S.multiplicity ⊆ S.aperySet := by
  intro x hx
  obtain ⟨hm, ha⟩ := Finset.mem_erase.mp hx
  exact S.atom_apery ((S.mem_atoms_iff _).mp ha) hm

end NSP14.NumericalSemigroup
