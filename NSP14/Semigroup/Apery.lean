module

public import NSP14.Semigroup.Basic

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- The least actual semigroup element in a residue class. -/
noncomputable def apery (r : Fin S.multiplicity) : ℕ := by
  classical
  exact Nat.find (S.residue_exists r)

theorem apery_spec (r : Fin S.multiplicity) :
    S.apery r ∈ S ∧ S.apery r % S.multiplicity = r.val := by
  classical
  exact Nat.find_spec (S.residue_exists r)

theorem apery_mem (r : Fin S.multiplicity) : S.apery r ∈ S := (S.apery_spec r).1
theorem apery_mod (r : Fin S.multiplicity) : S.apery r % S.multiplicity = r.val := (S.apery_spec r).2

theorem apery_min (r : Fin S.multiplicity) : IsAperyMin S.carrier S.multiplicity (S.apery r) := by
  classical
  refine ⟨S.apery_mem r, ?_⟩
  intro y hy hmod
  exact Nat.find_min' (S.residue_exists r) ⟨hy, hmod.trans (S.apery_mod r)⟩

theorem apery_injective : Function.Injective S.apery := by
  intro r t h
  apply Fin.ext
  have hmod := congrArg (fun x => x % S.multiplicity) h
  simpa only [S.apery_mod] using hmod

noncomputable def aperySet : Finset ℕ := by
  classical
  exact Finset.univ.image S.apery

theorem apery_card : S.aperySet.card = S.multiplicity := by
  classical
  simp [aperySet, Finset.card_image_of_injective _ S.apery_injective]

theorem mem_aperySet_iff (x : ℕ) : x ∈ S.aperySet ↔ IsAperyMin S.carrier S.multiplicity x := by
  classical
  constructor
  · intro h
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp h
    exact S.apery_min r
  · intro hx
    let r : Fin S.multiplicity := ⟨x % S.multiplicity, Nat.mod_lt _ S.multiplicity_pos⟩
    have h : x = S.apery r := apery_min_unique hx (S.apery_min r) (S.apery_mod r).symm
    exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, h.symm⟩

noncomputable def residue (x : ℕ) : Fin S.multiplicity := ⟨x % S.multiplicity, Nat.mod_lt _ S.multiplicity_pos⟩

theorem apery_le {x : ℕ} (hx : x ∈ S) : S.apery (S.residue x) ≤ x := by
  apply (S.apery_min (S.residue x)).2 x hx
  exact (S.apery_mod (S.residue x)).symm

/-- Every semigroup element has an actual Apéry representative plus a multiple of m. -/
theorem decomposition {x : ℕ} (hx : x ∈ S) :
    ∃ q : ℕ, x = S.apery (S.residue x) + q * S.multiplicity := by
  have hw := S.apery_le hx
  have hmod : S.apery (S.residue x) % S.multiplicity = x % S.multiplicity :=
    S.apery_mod (S.residue x)
  have hdvd : S.multiplicity ∣ x - S.apery (S.residue x) :=
    (Nat.modEq_iff_dvd' hw).mp hmod
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨q, ?_⟩
  nlinarith [Nat.sub_add_cancel hw]

theorem decomposition_unique {x : ℕ} {r t : Fin S.multiplicity} {p q : ℕ}
    (hp : x = S.apery r + p * S.multiplicity)
    (hq : x = S.apery t + q * S.multiplicity) : r = t ∧ p = q := by
  have hr : x % S.multiplicity = r.val := by rw [hp]; simp [Nat.add_mod, S.apery_mod, Nat.mod_eq_of_lt r.isLt]
  have ht : x % S.multiplicity = t.val := by rw [hq]; simp [Nat.add_mod, S.apery_mod, Nat.mod_eq_of_lt t.isLt]
  have hrt : r = t := Fin.ext (hr.symm.trans ht)
  subst t
  have hm := S.multiplicity_pos
  exact ⟨rfl, by nlinarith⟩

theorem apery_add_multiple (r : Fin S.multiplicity) (q : ℕ) :
    S.apery r + q * S.multiplicity ∈ S :=
  S.add_mem (S.apery_mem r) (S.multiple_mem q S.multiplicity_mem)

theorem zero_min : IsAperyMin S.carrier S.multiplicity 0 :=
  ⟨S.zero_mem, fun _ _ _ => Nat.zero_le _⟩

theorem zero_mem_apery : 0 ∈ S.aperySet := (S.mem_aperySet_iff 0).mpr S.zero_min

theorem multiplicity_not_apery : S.multiplicity ∉ S.aperySet := by
  intro h
  have hm := S.multiplicity_pos
  have hmin := (S.mem_aperySet_iff _).mp h
  have hle := hmin.2 0 S.zero_mem (by simp)
  omega

theorem apery_no_predecessor {x : ℕ} (hx : x ∈ S.aperySet) :
    ¬ ∃ y ∈ S, x = y + S.multiplicity := by
  rintro ⟨y, hy, heq⟩
  have hm := S.multiplicity_pos
  have hmin := (S.mem_aperySet_iff x).mp hx
  have hmod : y % S.multiplicity = x % S.multiplicity := by rw [heq]; simp
  have hle := hmin.2 y hy hmod
  omega

/-- Apéry membership is exactly absence of an m-predecessor in the same semigroup. -/
theorem mem_apery_iff_no_predecessor {x : ℕ} (hx : x ∈ S) :
    x ∈ S.aperySet ↔ ¬ ∃ y ∈ S, x = y + S.multiplicity := by
  constructor
  · exact S.apery_no_predecessor
  intro hn
  obtain ⟨q, hq⟩ := S.decomposition hx
  by_cases hzero : q = 0
  · subst q
    simp only [zero_mul, add_zero] at hq
    rw [hq]
    exact (S.mem_aperySet_iff _).mpr (S.apery_min _)
  have hq1 : 1 ≤ q := by omega
  have hy := S.apery_add_multiple (S.residue x) (q - 1)
  have heq : x = (S.apery (S.residue x) + (q - 1) * S.multiplicity) + S.multiplicity := by
    have hmul := congrArg (fun n => n * S.multiplicity) (Nat.sub_add_cancel hq1)
    nlinarith
  exact (hn ⟨_, hy, heq⟩).elim

end NSP14.NumericalSemigroup
