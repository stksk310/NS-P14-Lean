module

public import NSP14.Semigroup.OffsetPaths

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

theorem leastOffset_injective : Function.Injective S.leastOffset := by
  intro r t h
  apply Fin.ext
  have he := congrArg (fun x => x % S.multiplicity) h
  simpa only [(S.leastOffset_spec r).2, (S.leastOffset_spec t).2] using he

/-- Appending one actual atom increases the offset level by at most one. -/
theorem offsetLevel_step (r t : Fin S.multiplicity) (g : S.NonXAtom)
    (hb : S.leastOffset t = S.leastOffset r + (g.val.val - S.multiplicity)) :
    S.offsetLevel t ≤ S.offsetLevel r + 1 := by
  have hg := S.multiplicity_le g.val.property g.property.1.2.1
  have he : S.apery r + g.val.val =
      S.leastOffset t + (S.offsetLevel r + 1) * S.multiplicity := by
    rw [S.apery_eq_offset r, hb, Nat.add_mul, one_mul]
    omega
  have hmod : (S.apery r + g.val.val) % S.multiplicity = t.val := by
    rw [he, Nat.add_mul_mod_self_right]
    exact (S.leastOffset_spec t).2
  have hmin := (S.apery_min t).2 _ (S.add_mem (S.apery_mem r) g.val.property) (hmod.trans (S.apery_mod t).symm)
  have htarget := S.apery_eq_offset t
  have hm := S.multiplicity_pos
  rw [he] at hmin
  nlinarith

/-- At an atom residue a positive incoming prefix cannot attain equality. -/
theorem offsetLevel_step_atom (r t : Fin S.multiplicity) (g : S.NonXAtom)
    (hr : r.val ≠ 0) (ht : S.IsAtom (S.apery t))
    (hb : S.leastOffset t = S.leastOffset r + (g.val.val - S.multiplicity)) :
    S.offsetLevel t ≤ S.offsetLevel r := by
  have hle := S.offsetLevel_step r t g hb
  by_contra hn
  have heq : S.offsetLevel t = S.offsetLevel r + 1 := by omega
  have hg := S.multiplicity_le g.val.property g.property.1.2.1
  have he : S.apery t = S.apery r + g.val.val := by
    rw [S.apery_eq_offset t, heq, hb, S.apery_eq_offset r, Nat.add_mul, one_mul]
    omega
  have hp := S.apery_pos_of_residue_ne_zero r hr
  rcases ht.2.2 _ (S.apery_mem r) _ g.val.property he with h0 | h0
  · omega
  · have := g.property.1.2.1; omega

/-- Every level >=2 first reached along a least-offset path occurs at an actual
nonatom Apéry residue. Levels need not be monotone along the path. -/
theorem offsetLevel_high_exists (w : List S.NonXAtom) (r : Fin S.multiplicity)
    (hw : S.offsetWordValue w = S.leastOffset r) (n : ℕ)
    (hn : 2 ≤ n) (hlevel : n ≤ S.offsetLevel r) :
    ∃ t : Fin S.multiplicity, S.apery t ∈ S.highSet ∧ S.offsetLevel t = n := by
  induction w using List.reverseRecOn generalizing r with
  | nil =>
    have hb : S.leastOffset r = 0 := hw.symm
    have hr : r.val = 0 := by
      have hm := (S.leastOffset_spec r).2
      rw [hb, Nat.zero_mod] at hm
      exact hm.symm
    have := S.offsetLevel_zero r hr
    omega
  | @append_singleton w g ih =>
    let t := S.residue (S.offsetWordValue w)
    have ht : S.offsetWordValue w = S.leastOffset t := (S.leastOffset_prefix r w [g] hw).symm
    have hb : S.leastOffset r = S.leastOffset t + (g.val.val - S.multiplicity) := by
      rw [← hw, S.offsetWordValue_append, ht]
      rfl
    have hstep := S.offsetLevel_step t r g hb
    by_cases hprev : n ≤ S.offsetLevel t
    · exact ih t ht hprev
    have heq : S.offsetLevel r = n := by omega
    have ht0 : t.val ≠ 0 := by
      intro h0
      have := S.offsetLevel_zero t h0
      omega
    have hr0 : r.val ≠ 0 := by
      intro h0
      have := S.offsetLevel_zero r h0
      omega
    have hnot : ¬ S.IsAtom (S.apery r) := by
      intro ha
      have := S.offsetLevel_step_atom t r g ht0 ha hb
      omega
    have horder : 2 ≤ S.order (S.apery r) := by
      have hp := S.order_pos (S.apery_mem r) (S.apery_pos_of_residue_ne_zero r hr0)
      have hne : S.order (S.apery r) ≠ 1 := fun h =>
        hnot ((S.order_one_iff_atom (S.apery_mem r)).1 h)
      omega
    exact ⟨r, Finset.mem_filter.mpr ⟨(S.mem_aperySet_iff _).2 (S.apery_min r), horder⟩, heq⟩

/-- The uniform level bound counts distinct actual nonatom residues, rather than
replacing a level by the possibly smaller order of its Apéry representative. -/
theorem offsetLevel_le_deficit_succ (r : Fin S.multiplicity) : S.offsetLevel r ≤ S.deficit + 1 := by
  let f : Fin (S.offsetLevel r - 1) → Fin S.multiplicity := fun i =>
    (S.offsetLevel_high_exists (S.leastOffsetWord r) r (S.leastOffsetWord_spec r).1
      (i.val + 2) (by omega) (by have := i.isLt; omega)).choose
  have hf : ∀ i, S.apery (f i) ∈ S.highSet ∧ S.offsetLevel (f i) = i.val + 2 := by
    intro i
    exact (S.offsetLevel_high_exists (S.leastOffsetWord r) r (S.leastOffsetWord_spec r).1
      (i.val + 2) (by omega) (by have := i.isLt; omega)).choose_spec
  have hc : (Finset.univ : Finset (Fin (S.offsetLevel r - 1))).card ≤ S.highSet.card := by
    apply Finset.card_le_card_of_injOn (fun i => S.apery (f i))
    · intro i _; exact (hf i).1
    · intro i _ j _ hij
      have h := congrArg S.offsetLevel (S.apery_injective hij)
      rw [(hf i).2, (hf j).2] at h
      exact Fin.ext (by omega)
  rw [Finset.card_univ, Fintype.card_fin, S.highSet_card] at hc
  omega

end NSP14.NumericalSemigroup
