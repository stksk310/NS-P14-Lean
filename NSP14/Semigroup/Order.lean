module

public import NSP14.Semigroup.Atoms
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open scoped BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

theorem sum_mem {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ∈ S) :
    ∑ i ∈ s, f i ∈ S := S.carrier.sum_mem hf

/-- A decomposition into n positive actual semigroup elements. -/
def HasLength (x n : ℕ) : Prop :=
  ∃ f : Fin n → ℕ, (∀ i, f i ∈ S ∧ 0 < f i) ∧ ∑ i, f i = x

theorem length_zero : S.HasLength 0 0 := by
  refine ⟨Fin.elim0, fun i => Fin.elim0 i, ?_⟩
  simp

theorem length_one {x : ℕ} (hx : x ∈ S) (hpos : 0 < x) : S.HasLength x 1 :=
  ⟨fun _ => x, fun _ => ⟨hx, hpos⟩, by simp⟩

theorem length_le {x n : ℕ} (h : S.HasLength x n) : n ≤ x := by
  obtain ⟨f, hf, heq⟩ := h
  have hle : (∑ _i : Fin n, 1) ≤ ∑ i, f i :=
    Finset.sum_le_sum (fun i _ => by have := (hf i).2; omega)
  simpa [heq] using hle

theorem length_multiplicity_bound {x n : ℕ} (h : S.HasLength x n) : n * S.multiplicity ≤ x := by
  obtain ⟨f, hf, heq⟩ := h
  have hle : (∑ _i : Fin n, S.multiplicity) ≤ ∑ i, f i :=
    Finset.sum_le_sum (fun i _ => S.multiplicity_le (hf i).1 (hf i).2)
  simpa [heq] using hle

theorem length_exists {x : ℕ} (hx : x ∈ S) : ∃ n, n ≤ x ∧ S.HasLength x n := by
  by_cases h0 : x = 0
  · subst x; exact ⟨0, le_rfl, S.length_zero⟩
  · exact ⟨1, by omega, S.length_one hx (by omega)⟩

/-- Maximum positive-element decomposition length; its existence is proved below. -/
noncomputable def order (x : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (S.HasLength x) x

theorem order_length {x : ℕ} (hx : x ∈ S) : S.HasLength x (S.order x) := by
  classical
  obtain ⟨n, hn, hlen⟩ := S.length_exists hx
  exact Nat.findGreatest_spec hn hlen

theorem length_le_order {x n : ℕ} (h : S.HasLength x n) : n ≤ S.order x := by
  classical
  exact Nat.le_findGreatest (S.length_le h) h

theorem order_bound {x : ℕ} (hx : x ∈ S) : S.order x * S.multiplicity ≤ x :=
  S.length_multiplicity_bound (S.order_length hx)

theorem order_zero : S.order 0 = 0 := by
  classical
  exact Nat.le_zero.mp (Nat.findGreatest_le 0)

theorem order_pos {x : ℕ} (hx : x ∈ S) (hpos : 0 < x) : 0 < S.order x := by
  have h := S.length_le_order (S.length_one hx hpos)
  omega

theorem order_eq_zero_iff {x : ℕ} (hx : x ∈ S) : S.order x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hn
    have hpos := S.order_pos hx (by omega)
    omega
  · rintro rfl; exact S.order_zero

theorem length_add {x y n k : ℕ} (hx : S.HasLength x n) (hy : S.HasLength y k) :
    S.HasLength (x + y) (n + k) := by
  obtain ⟨f, hf, hfx⟩ := hx
  obtain ⟨g, hg, hgy⟩ := hy
  refine ⟨Fin.addCases f g, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hf j
    · simpa using hg j
  · simpa [Fin.sum_univ_add] using congrArg₂ (· + ·) hfx hgy

theorem order_add {x y : ℕ} (hx : x ∈ S) (hy : y ∈ S) :
    S.order x + S.order y ≤ S.order (x + y) :=
  S.length_le_order (S.length_add (S.order_length hx) (S.order_length hy))

theorem order_multiplicity : S.order S.multiplicity = 1 := by
  have hp := S.order_pos S.multiplicity_mem S.multiplicity_pos
  have hb := S.order_bound S.multiplicity_mem
  have hm := S.multiplicity_pos
  by_contra hne
  have htwo : 2 ≤ S.order S.multiplicity := by omega
  have hmul := Nat.mul_le_mul_right S.multiplicity htwo
  nlinarith

theorem order_add_multiplicity {x : ℕ} (hx : x ∈ S) :
    S.order x + 1 ≤ S.order (x + S.multiplicity) := by
  simpa [S.order_multiplicity] using S.order_add hx S.multiplicity_mem

theorem atom_length_bound {x n : ℕ} (hx : S.IsAtom x) (h : S.HasLength x n) : n ≤ 1 := by
  obtain ⟨f, hf, heq⟩ := h
  by_contra hn
  have hn2 : 2 ≤ n := by omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have hk : 0 < k := by omega
  let i0 : Fin k := ⟨0, hk⟩
  have hrest : (∑ i : Fin k, f i.succ) ∈ S := S.sum_mem _ _ (fun i _ => (hf i.succ).1)
  have hrestpos : 0 < ∑ i : Fin k, f i.succ := by
    apply Finset.sum_pos'
    · intro i _; exact Nat.zero_le _
    · exact ⟨i0, Finset.mem_univ _, (hf i0.succ).2⟩
  rw [Fin.sum_univ_succ] at heq
  rcases hx.2.2 (f 0) (hf 0).1 _ hrest heq.symm with h0 | h0
  · have := (hf 0).2; omega
  · omega

theorem atom_order {x : ℕ} (hx : S.IsAtom x) : S.order x = 1 := by
  have hle := S.atom_length_bound hx (S.order_length hx.1)
  have hpos := S.order_pos hx.1 hx.2.1
  omega

theorem order_one_iff_atom {x : ℕ} (hx : x ∈ S) : S.order x = 1 ↔ S.IsAtom x := by
  constructor
  · intro horder
    have hpos : 0 < x := by
      by_contra h
      have hx0 : x = 0 := by omega
      subst x
      have := S.order_zero
      omega
    refine ⟨hx, hpos, ?_⟩
    intro u hu v hv heq
    by_cases h0 : u = 0
    · exact Or.inl h0
    by_cases h1 : v = 0
    · exact Or.inr h1
    have huord := S.order_pos hu (by omega)
    have hvord := S.order_pos hv (by omega)
    have hadd := S.order_add hu hv
    rw [← heq, horder] at hadd
    omega
  · exact S.atom_order

theorem order_sum {ι : Type*} (s : Finset ι) (f : ι → ℕ) (hf : ∀ i ∈ s, f i ∈ S) :
    ∑ i ∈ s, S.order (f i) ≤ S.order (∑ i ∈ s, f i) := by
  classical
  revert hf
  induction s using Finset.induction with
  | empty => intro _; simp [S.order_zero]
  | @insert a s ha ih =>
    intro hf
    have hfa := hf a (Finset.mem_insert_self _ _)
    have hfs : ∀ i ∈ s, f i ∈ S := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hsum := S.sum_mem s f hfs
    have hi := ih hfs
    have hadd := S.order_add hfa hsum
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    omega

/-- Every longest positive-element decomposition consists of actual atoms. -/
theorem longest_factors_atoms {x : ℕ}
    (f : Fin (S.order x) → ℕ) (hf : ∀ i, f i ∈ S ∧ 0 < f i) (hsum : ∑ i, f i = x) :
    ∀ i, S.IsAtom (f i) := by
  intro i
  have horders : (∑ j, S.order (f j)) ≤ S.order x := by
    simpa [hsum] using S.order_sum Finset.univ f (fun j _ => (hf j).1)
  have hrest : (∑ _j ∈ (Finset.univ : Finset (Fin (S.order x))).erase i, 1) ≤
      ∑ j ∈ (Finset.univ : Finset (Fin (S.order x))).erase i, S.order (f j) := by
    apply Finset.sum_le_sum
    intro j _
    have := S.order_pos (hf j).1 (hf j).2
    omega
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin (S.order x)))
    (fun j => S.order (f j)) (Finset.mem_univ i)
  have hn : 0 < S.order x := by have := i.isLt; omega
  have hpos := S.order_pos (hf i).1 (hf i).2
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hrest
  apply (S.order_one_iff_atom (hf i).1).mp
  omega

/-- Thus the constructed order is exactly the longest minimal-generator representation length. -/
theorem order_realized_by_atoms {x : ℕ} (hx : x ∈ S) :
    ∃ f : Fin (S.order x) → ℕ, (∀ i, S.IsAtom (f i)) ∧ ∑ i, f i = x := by
  obtain ⟨f, hf, hsum⟩ := S.order_length hx
  exact ⟨f, S.longest_factors_atoms f hf hsum, hsum⟩

theorem atomic_length_le {x n : ℕ} (f : Fin n → ℕ) (hf : ∀ i, S.IsAtom (f i))
    (hsum : ∑ i, f i = x) : n ≤ S.order x :=
  S.length_le_order ⟨f, fun i => ⟨(hf i).1, (hf i).2.1⟩, hsum⟩

end NSP14.NumericalSemigroup
