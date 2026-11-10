module

public import NSP14.Semigroup.Heads
public import Mathlib.Data.Finset.Max

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- A realised offset. Factors are positive semigroup elements; minimality below
forces shortest realisations to use precisely the non-multiplicity atoms. -/
def OffsetRealized (b : ℕ) : Prop :=
  ∃ n : ℕ, S.HasLength (b + n * S.multiplicity) n

theorem length_offset {x n : ℕ} (h : S.HasLength x n) :
    S.HasLength (x - n * S.multiplicity + n * S.multiplicity) n := by
  rwa [Nat.sub_add_cancel (S.length_multiplicity_bound h)]

theorem offset_exists (r : Fin S.multiplicity) :
    ∃ b, S.OffsetRealized b ∧ b % S.multiplicity = r.val := by
  let n := S.order (S.apery r)
  have hl := S.order_length (S.apery_mem r)
  have hb := S.length_multiplicity_bound hl
  refine ⟨S.apery r - n * S.multiplicity, ⟨n, S.length_offset hl⟩, ?_⟩
  have he : S.apery r - n * S.multiplicity + n * S.multiplicity = S.apery r :=
    Nat.sub_add_cancel hb
  have hm := congrArg (fun a => a % S.multiplicity) he
  simpa only [Nat.add_mul_mod_self_right, S.apery_mod] using hm

/-- Least realised offset in the actual residue class. -/
noncomputable def leastOffset (r : Fin S.multiplicity) : ℕ :=
  Nat.find (S.offset_exists r)

theorem leastOffset_spec (r : Fin S.multiplicity) :
    S.OffsetRealized (S.leastOffset r) ∧ S.leastOffset r % S.multiplicity = r.val :=
  Nat.find_spec (S.offset_exists r)

theorem leastOffset_le (r : Fin S.multiplicity) {b : ℕ}
    (hb : S.OffsetRealized b) (hr : b % S.multiplicity = r.val) : S.leastOffset r ≤ b :=
  Nat.find_min' (S.offset_exists r) ⟨hb, hr⟩

/-- Shortest representation at the least offset. -/
noncomputable def leastOffsetLength (r : Fin S.multiplicity) : ℕ :=
  Nat.find (S.leastOffset_spec r).1

theorem leastOffsetLength_spec (r : Fin S.multiplicity) :
    S.HasLength (S.leastOffset r + S.leastOffsetLength r * S.multiplicity)
      (S.leastOffsetLength r) := Nat.find_spec (S.leastOffset_spec r).1

theorem leastOffsetLength_le (r : Fin S.multiplicity) {n : ℕ}
    (h : S.HasLength (S.leastOffset r + n * S.multiplicity) n) :
    S.leastOffsetLength r ≤ n := Nat.find_min' (S.leastOffset_spec r).1 h

theorem leastOffset_order_bound {x : ℕ} (hx : x ∈ S) (r : Fin S.multiplicity)
    (hr : x % S.multiplicity = r.val) :
    S.leastOffset r + S.order x * S.multiplicity ≤ x := by
  have hlen := S.order_length hx
  have hb := S.length_multiplicity_bound hlen
  have he := Nat.sub_add_cancel hb
  have hmod := congrArg (fun a => a % S.multiplicity) he
  have hoff : (x - S.order x * S.multiplicity) % S.multiplicity = r.val := by
    simpa only [Nat.add_mul_mod_self_right, hr] using hmod
  have hmin := S.leastOffset_le r ⟨_, S.length_offset hlen⟩ hoff
  omega

theorem leastOffset_le_apery (r : Fin S.multiplicity) : S.leastOffset r ≤ S.apery r := by
  have := S.leastOffset_order_bound (S.apery_mem r) r (S.apery_mod r)
  omega

noncomputable def offsetLevel (r : Fin S.multiplicity) : ℕ :=
  (S.apery r - S.leastOffset r) / S.multiplicity

theorem apery_eq_offset (r : Fin S.multiplicity) :
    S.apery r = S.leastOffset r + S.offsetLevel r * S.multiplicity := by
  have hle := S.leastOffset_le_apery r
  have hmod : S.leastOffset r % S.multiplicity = S.apery r % S.multiplicity :=
    (S.leastOffset_spec r).2.trans (S.apery_mod r).symm
  have hdvd := (Nat.modEq_iff_dvd' hle).mp hmod
  have hdiv := Nat.div_mul_cancel hdvd
  change S.apery r = S.leastOffset r +
    ((S.apery r - S.leastOffset r) / S.multiplicity) * S.multiplicity
  omega

theorem order_apery_le_offsetLevel (r : Fin S.multiplicity) :
    S.order (S.apery r) ≤ S.offsetLevel r := by
  have hb := S.leastOffset_order_bound (S.apery_mem r) r (S.apery_mod r)
  have he := S.apery_eq_offset r
  have hm := S.multiplicity_pos
  nlinarith

theorem offsetLevel_le_length (r : Fin S.multiplicity) :
    S.offsetLevel r ≤ S.leastOffsetLength r := by
  obtain ⟨f, hf, heq⟩ := S.leastOffsetLength_spec r
  have hmem := S.sum_mem Finset.univ f (fun i _ => (hf i).1)
  rw [heq] at hmem
  have hmin := (S.apery_min r).2 _ hmem (by
    simpa only [Nat.add_mul_mod_self_right, S.apery_mod] using (S.leastOffset_spec r).2)
  have he := S.apery_eq_offset r
  have hm := S.multiplicity_pos
  nlinarith

theorem length_multiple (q : ℕ) : S.HasLength (q * S.multiplicity) q := by
  refine ⟨fun _ => S.multiplicity, fun _ => ⟨S.multiplicity_mem, S.multiplicity_pos⟩, ?_⟩
  simp

theorem order_multiple (q : ℕ) : S.order (q * S.multiplicity) = q := by
  have hl := S.length_le_order (S.length_multiple q)
  have hb := S.order_bound (S.multiple_mem q S.multiplicity_mem)
  have hm := S.multiplicity_pos
  nlinarith

/-- The explicit least-offset threshold, with no finite-dimensionality input. -/
theorem order_stabilization (r : Fin S.multiplicity) (q : ℕ)
    (hq : S.leastOffsetLength r ≤ S.offsetLevel r + q) :
    S.order (S.apery r + q * S.multiplicity) = S.offsetLevel r + q := by
  have he := S.apery_eq_offset r
  have hm := S.multiplicity_pos
  have hu := S.leastOffset_order_bound (S.apery_add_multiple r q) r (by
    simp only [Nat.add_mul_mod_self_right, S.apery_mod])
  have hl := S.length_add (S.leastOffsetLength_spec r)
    (S.length_multiple (S.offsetLevel r + q - S.leastOffsetLength r))
  have htotal : S.leastOffsetLength r +
      (S.offsetLevel r + q - S.leastOffsetLength r) = S.offsetLevel r + q := by omega
  rw [htotal] at hl
  have hval : S.leastOffset r + S.leastOffsetLength r * S.multiplicity +
      (S.offsetLevel r + q - S.leastOffsetLength r) * S.multiplicity =
      S.apery r + q * S.multiplicity := by
    rw [Nat.add_assoc, ← Nat.add_mul, htotal]
    nlinarith
  rw [hval] at hl
  have hlo := S.length_le_order hl
  nlinarith

/-- A finite bound uniform over all actual residue classes. The bound is deliberately
loose; it is used only to prove finiteness, never as the numerical resource budget. -/
noncomputable def stabilizationBound : ℕ :=
  Finset.univ.sup (fun r : Fin S.multiplicity =>
    S.apery r + S.leastOffsetLength r * S.multiplicity)

theorem not_terminal_of_stable {x : ℕ} (hx : x ∈ S) (hb : S.stabilizationBound ≤ x) :
    ¬ S.Terminal x := by
  obtain ⟨q, hq⟩ := S.decomposition hx
  let r := S.residue x
  have hr : S.apery r + S.leastOffsetLength r * S.multiplicity ≤ S.stabilizationBound :=
    Finset.le_sup (f := fun t : Fin S.multiplicity =>
      S.apery t + S.leastOffsetLength t * S.multiplicity) (Finset.mem_univ r)
  have hm := S.multiplicity_pos
  have hlen : S.leastOffsetLength r ≤ q := by
    change x = S.apery r + q * S.multiplicity at hq
    nlinarith
  have ho := S.order_stabilization r q (by omega)
  have ho' := S.order_stabilization r (q + 1) (by omega)
  have hval : x + S.multiplicity = S.apery r + (q + 1) * S.multiplicity := by
    change x = S.apery r + q * S.multiplicity at hq
    nlinarith
  rw [← hq] at ho
  rw [← hval] at ho'
  rintro ⟨_, ht⟩
  omega

theorem terminal_lt_stabilizationBound {x : ℕ} (hx : S.Terminal x) :
    x < S.stabilizationBound := by
  by_contra hn
  exact S.not_terminal_of_stable hx.1 (by omega) hx

theorem terminal_finite : Set.Finite {x | S.Terminal x} :=
  (Finset.finite_toSet (Finset.range S.stabilizationBound)).subset
    (fun _ hx => Finset.mem_range.mpr (S.terminal_lt_stabilizationBound hx))

end NSP14.NumericalSemigroup
