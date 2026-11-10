module

public import NSP14.Semigroup.TowerIntervals

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

theorem order_add_multiple {x : ℕ} (hx : x ∈ S) (q : ℕ) :
    S.order x + q ≤ S.order (x + q * S.multiplicity) := by
  have h := S.order_add hx (S.multiple_mem q S.multiplicity_mem)
  rwa [S.order_multiple] at h

theorem same_residue_add_multiple {x y : ℕ} (hxy : x ≤ y)
    (hmod : x % S.multiplicity = y % S.multiplicity) :
    ∃ q : ℕ, y = x + q * S.multiplicity := by
  obtain ⟨q,hq⟩ := (Nat.modEq_iff_dvd' hxy).mp hmod
  exact ⟨q,by nlinarith [Nat.sub_add_cancel hxy]⟩

theorem head_zero_residue (h : S.HeadExponent) (hmod : h.val.val % S.multiplicity = 0) :
    h.val.val = 0 := by
  by_contra hn
  obtain ⟨q,hq⟩ := Nat.dvd_of_mod_eq_zero hmod
  have hm := S.multiplicity_pos
  have hq1 : 1 ≤ q := by
    by_contra hq0
    have : q = 0 := by omega
    apply hn
    change h.val.val = S.multiplicity * q at hq
    simpa only [this, Nat.mul_zero] using hq
  have he : h.val.val = (q-1) * S.multiplicity + S.multiplicity := by
    calc
      _ = q * S.multiplicity := hq.trans (Nat.mul_comm _ _)
      _ = _ := by conv_lhs => rw [← Nat.sub_add_cancel hq1]; rw [Nat.add_mul]; simp
  have ho : S.order h.val.val = S.order ((q-1) * S.multiplicity) + 1 := by
    rw [hq, Nat.mul_comm S.multiplicity q, S.order_multiple, S.order_multiple]
    omega
  exact h.property.2 ⟨(q-1) * S.multiplicity,S.multiple_mem _ S.multiplicity_mem,he,ho⟩

theorem HeadContributes.order_upper {t : ℕ} {h : S.HeadExponent} (hc : S.HeadContributes t h) :
    t + 2 ≤ S.order h.val.val := by
  obtain ⟨s,hs,_,_,ho⟩ := hc
  omega

/-- Distinct contributing intervals in one residue cannot overlap. -/
theorem contributing_residue_injective (t : ℕ) :
    Function.Injective (fun h : S.ContributingHead t => S.residue h.val.val.val) := by
  intro h j he
  have hmod : h.val.val.val % S.multiplicity = j.val.val.val % S.multiplicity := congrArg Fin.val he
  have hnonlt : ∀ (a b : S.ContributingHead t),
      a.val.val.val % S.multiplicity = b.val.val.val % S.multiplicity →
      ¬a.val.val.val < b.val.val.val := by
    intro a b hmod hab
    obtain ⟨q,hq⟩ := S.same_residue_add_multiple (Nat.le_of_lt hab) hmod
    have hm := S.multiplicity_pos
    have hq1 : 1 ≤ q := by nlinarith
    have hb : b.val.val.val ∉ S.aperySet := by
      intro hb
      have hmin := ((S.mem_aperySet_iff _).1 hb).2 _ a.val.val.property hmod
      omega
    have hlower := (S.headContributes_nonapery t b.val hb).1 b.property |>.1
    have hupper := HeadContributes.order_upper S a.property
    have hp : b.val.val.val - S.multiplicity =
        a.val.val.val + (q-1) * S.multiplicity := by
      have heq : b.val.val.val = a.val.val.val + (q-1) * S.multiplicity + S.multiplicity := by
        calc
          _ = a.val.val.val + q * S.multiplicity := hq
          _ = _ := by conv_lhs => rw [← Nat.sub_add_cancel hq1]; rw [Nat.add_mul]; simp only [Nat.one_mul]; exact (Nat.add_assoc _ _ _).symm
      omega
    have ho := S.order_add_multiple a.val.val.property (q-1)
    rw [← hp] at ho
    omega
  have hv : h.val.val.val = j.val.val.val := by
    have h1 := hnonlt h j hmod
    have h2 := hnonlt j h hmod.symm
    omega
  exact Subtype.ext (Subtype.ext (Subtype.ext hv))

/-- Every H_t is bounded by all nonzero actual residues, not by a cutoff. -/
theorem towerResource_le_multiplicity (k : Type*) [Field k] (t : ℕ) :
    S.towerResource k t ≤ S.multiplicity - 1 := by
  let z : Fin S.multiplicity := ⟨0,S.multiplicity_pos⟩
  let f : S.ContributingHead t → ↥((Finset.univ : Finset (Fin S.multiplicity)).erase z) := fun h =>
    ⟨S.residue h.val.val.val,Finset.mem_erase.mpr ⟨by
      intro he
      have hmod : h.val.val.val % S.multiplicity = 0 := congrArg Fin.val he
      have hzero := S.head_zero_residue h.val hmod
      have hu := HeadContributes.order_upper S h.property
      rw [hzero,S.order_zero] at hu
      omega,Finset.mem_univ _⟩⟩
  have hi : Function.Injective f := fun a b he => S.contributing_residue_injective t
    (congrArg Subtype.val he)
  have hc := Fintype.card_le_of_injective f hi
  rw [S.towerResource_card k]
  simpa only [Fintype.card_coe,Finset.card_erase_of_mem (Finset.mem_univ z),
    Finset.card_univ,Fintype.card_fin] using hc

end NSP14.NumericalSemigroup
