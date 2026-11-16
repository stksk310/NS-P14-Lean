module

public import NSP14.Semigroup.OffsetTelescoping
public import Mathlib.Data.List.TakeDrop

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

noncomputable def offsetWordValue (w : List S.NonXAtom) : ℕ :=
  (w.map (fun a => a.val.val - S.multiplicity)).sum

theorem nonXAtom_offset_pos (a : S.NonXAtom) : 0 < a.val.val - S.multiplicity := by
  have hle := S.multiplicity_le a.val.property a.property.1.2.1
  have hne := a.property.2
  omega

@[simp] theorem offsetWordValue_nil : S.offsetWordValue [] = 0 := rfl
@[simp] theorem offsetWordValue_cons (a : S.NonXAtom) (w : List S.NonXAtom) :
    S.offsetWordValue (a :: w) = a.val.val - S.multiplicity + S.offsetWordValue w := rfl
@[simp] theorem offsetWordValue_append (u v : List S.NonXAtom) :
    S.offsetWordValue (u ++ v) = S.offsetWordValue u + S.offsetWordValue v := by
  simp [offsetWordValue, List.map_append, List.sum_append]

theorem offsetWord_weight (w : List S.NonXAtom) :
    (w.map (fun a => a.val.val)).sum = S.offsetWordValue w + w.length * S.multiplicity := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := S.multiplicity_le a.val.property a.property.1.2.1
    simp only [List.map_cons, List.sum_cons, offsetWordValue_cons, List.length_cons]
    rw [ih, Nat.add_mul]
    omega

theorem offsetWord_length (w : List S.NonXAtom) :
    S.HasLength (S.offsetWordValue w + w.length * S.multiplicity) w.length := by
  refine ⟨fun i => (w.get i).val.val,
    fun i => ⟨(w.get i).val.property, (w.get i).property.1.2.1⟩, ?_⟩
  rw [← S.offsetWord_weight]
  have h : List.ofFn (fun i => (w.get i).val.val) = w.map (fun a => a.val.val) := by
    conv_rhs => rw [← List.ofFn_get w]
    rw [List.map_ofFn]
    rfl
  rw [← List.sum_ofFn, h]

theorem offsetWord_realized (w : List S.NonXAtom) : S.OffsetRealized (S.offsetWordValue w) :=
  ⟨w.length, S.offsetWord_length w⟩

theorem leastOffsetWord_exists (r : Fin S.multiplicity) :
    ∃ w : List S.NonXAtom,
      S.offsetWordValue w = S.leastOffset r ∧ w.length = S.leastOffsetLength r := by
  obtain ⟨f, hf, hs⟩ := S.leastOffsetLength_spec r
  have hat := S.shortest_offset_factors r f hf hs
  let g : Fin (S.leastOffsetLength r) → S.NonXAtom :=
    fun i => ⟨⟨f i, (hf i).1⟩, hat i⟩
  refine ⟨List.ofFn g, ?_, List.length_ofFn⟩
  have hw := S.offsetWord_weight (List.ofFn g)
  have hsum : ((List.ofFn g).map (fun a => a.val.val)).sum =
      S.leastOffset r + S.leastOffsetLength r * S.multiplicity := by
    rw [List.map_ofFn, List.sum_ofFn]
    exact hs
  rw [List.length_ofFn, hsum] at hw
  omega

noncomputable def leastOffsetWord (r : Fin S.multiplicity) : List S.NonXAtom :=
  (S.leastOffsetWord_exists r).choose

theorem leastOffsetWord_spec (r : Fin S.multiplicity) :
    S.offsetWordValue (S.leastOffsetWord r) = S.leastOffset r ∧
      (S.leastOffsetWord r).length = S.leastOffsetLength r :=
  (S.leastOffsetWord_exists r).choose_spec

theorem offsetRealized_add {a b : ℕ} (ha : S.OffsetRealized a) (hb : S.OffsetRealized b) :
    S.OffsetRealized (a + b) := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨k, hk⟩ := hb
  have he : (a + n * S.multiplicity) + (b + k * S.multiplicity) =
      a + b + (n + k) * S.multiplicity := by ring
  exact ⟨n + k, he ▸ S.length_add hn hk⟩

/-- Replacing a prefix by a smaller offset contradicts the minimality of the
whole actual path. No word-order or genericity hypothesis is used. -/
theorem leastOffset_prefix (r : Fin S.multiplicity) (u v : List S.NonXAtom)
    (hw : S.offsetWordValue (u ++ v) = S.leastOffset r) :
    S.leastOffset (S.residue (S.offsetWordValue u)) = S.offsetWordValue u := by
  let t := S.residue (S.offsetWordValue u)
  have hle := S.leastOffset_le t (S.offsetWord_realized u) rfl
  have hrep := S.offsetRealized_add (S.leastOffset_spec t).1 (S.offsetWord_realized v)
  have ht : S.leastOffset t % S.multiplicity = S.offsetWordValue u % S.multiplicity :=
    (S.leastOffset_spec t).2
  have hmod : (S.leastOffset t + S.offsetWordValue v) % S.multiplicity = r.val := by
    rw [Nat.add_mod, ht, ← Nat.add_mod, ← S.offsetWordValue_append, hw]
    exact (S.leastOffset_spec r).2
  have hmin := S.leastOffset_le r hrep hmod
  rw [S.offsetWordValue_append] at hw
  dsimp only [t] at hle hmin
  omega

/-- Positive offsets make prefix weights strictly increasing. -/
theorem offsetWord_take_strict (w : List S.NonXAtom) {i j : ℕ}
    (hij : i < j) (hj : j ≤ w.length) :
    S.offsetWordValue (w.take i) < S.offsetWordValue (w.take j) := by
  induction w generalizing i j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons a w ih =>
    cases i with
    | zero =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      simp only [List.take_zero, offsetWordValue_nil, List.take_succ_cons, offsetWordValue_cons]
      have := S.nonXAtom_offset_pos a
      omega
    | succ i =>
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      simp only [List.take_succ_cons, offsetWordValue_cons]
      have hk : k ≤ w.length := by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hj
      exact Nat.add_lt_add_left (ih (by omega) hk) _

/-- Every prefix of a least-offset path is itself least in its residue. -/
theorem leastOffset_take (r : Fin S.multiplicity) (i : ℕ) :
    S.leastOffset (S.residue (S.offsetWordValue ((S.leastOffsetWord r).take i))) =
      S.offsetWordValue ((S.leastOffsetWord r).take i) := by
  apply S.leastOffset_prefix r _ ((S.leastOffsetWord r).drop i)
  rw [List.take_append_drop, (S.leastOffsetWord_spec r).1]

/-- Prefixes, including the empty prefix, have pairwise distinct residues. -/
theorem leastOffset_prefix_injective (r : Fin S.multiplicity) :
    Function.Injective (fun i : Fin ((S.leastOffsetWord r).length + 1) =>
      S.residue (S.offsetWordValue ((S.leastOffsetWord r).take i.val))) := by
  intro i j he
  have hval : S.offsetWordValue ((S.leastOffsetWord r).take i.val) =
      S.offsetWordValue ((S.leastOffsetWord r).take j.val) := by
    rw [← S.leastOffset_take r i.val, ← S.leastOffset_take r j.val]
    exact congrArg S.leastOffset he
  apply Fin.ext
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · have hlt := S.offsetWord_take_strict (S.leastOffsetWord r) hij (by have := j.isLt; omega)
    omega
  · have hlt := S.offsetWord_take_strict (S.leastOffsetWord r) hji (by have := i.isLt; omega)
    omega

/-- The actual shortest least-offset path has no cycle, even when m=1. -/
theorem leastOffsetLength_lt_multiplicity (r : Fin S.multiplicity) :
    S.leastOffsetLength r < S.multiplicity := by
  have hc := Fintype.card_le_of_injective _ (S.leastOffset_prefix_injective r)
  simp only [Fintype.card_fin, (S.leastOffsetWord_spec r).2] at hc
  omega

end NSP14.NumericalSemigroup
