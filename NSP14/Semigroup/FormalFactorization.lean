module

public import NSP14.Semigroup.FormalOrder

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

noncomputable instance degreeExponentFintype (n : ℕ) : Fintype (S.DegreeExponent n) := Fintype.ofFinite _

/-- Choose a prefix of a longest expression, not a least-value divisor. -/
noncomputable def orderPrefix (n : ℕ) (v : S.carrier) : S.carrier :=
  if h : n ≤ S.order v.val then (S.order_live_split v n h).choose else 0

theorem orderPrefix_spec (n : ℕ) (v : S.carrier) (h : n ≤ S.order v.val) :
    ∃ w : S.carrier, v = S.orderPrefix n v + w ∧
      S.order (S.orderPrefix n v).val = n ∧ S.order w.val = S.order v.val - n := by
  simpa only [orderPrefix, dite_eq_left h] using (S.order_live_split v n h).choose_spec

variable (k : Type*) [CommRing k]

/-- Collect the infinitely many coefficients with a fixed chosen prefix. -/
noncomputable def formalFactor (n : ℕ) (f : S.FormalSemigroupRing k)
    (u : S.DegreeExponent n) : S.FormalSemigroupRing k :=
  ⟨PowerSeries.mk (fun w => if hw : w ∈ S then
      if S.orderPrefix n (u.val + ⟨w,hw⟩) = u.val then
        PowerSeries.coeff (u.val.val+w) f.val else 0 else 0), by
    intro w hw
    simp [PowerSeries.coeff_mk, hw]⟩

theorem formalMonomial_mul_coeff (u : S.carrier) (g : S.FormalSemigroupRing k) (v : ℕ) :
    PowerSeries.coeff v (S.formalMonomial k u 1 * g).val =
      if u.val ≤ v then PowerSeries.coeff (v-u.val) g.val else 0 := by
  change PowerSeries.coeff v (PowerSeries.monomial u.val 1 * g.val) = _
  rw [← PowerSeries.X_pow_eq]
  exact PowerSeries.coeff_X_pow_mul' _ _ _

/-- A finite sum suffices even for an infinite formal series. -/
theorem formal_order_factorization (n : ℕ) (f : S.FormalSemigroupRing k)
    (hf : f ∈ S.formalOrderIdeal k n) :
    f = ∑ u : S.DegreeExponent n, S.formalMonomial k u.val 1 * S.formalFactor k n f u := by
  apply Subtype.ext
  apply PowerSeries.ext
  intro v
  change PowerSeries.coeff v f.val =
    PowerSeries.coeff v ((S.formalSeriesAlgebra k).val (∑ u : S.DegreeExponent n,
      S.formalMonomial k u.val 1 * S.formalFactor k n f u))
  simp only [map_sum]
  by_cases hv : v ∈ S
  · by_cases hn : n ≤ S.order v
    · obtain ⟨w,he,ho,_⟩ := S.orderPrefix_spec n ⟨v,hv⟩ hn
      let u : S.DegreeExponent n := ⟨S.orderPrefix n ⟨v,hv⟩,ho⟩
      have hvu : v = u.val.val + w.val := congrArg Subtype.val he
      have hu : u.val.val ≤ v := by omega
      rw [Finset.sum_eq_single u]
      · erw [S.formalMonomial_mul_coeff k, ite_eq_left_iff.mpr (fun h => (h hu).elim)]
        simp only [formalFactor, PowerSeries.coeff_mk]
        have hw : v-u.val.val ∈ S := by
          rw [show v-u.val.val = w.val by omega]
          exact w.property
        rw [dite_eq_left hw]
        have he' : u.val + ⟨v-u.val.val,hw⟩ = ⟨v,hv⟩ := by
          apply Subtype.ext; change u.val.val+(v-u.val.val)=v; omega
        rw [he', ite_eq_left_iff.mpr (fun h => (h rfl).elim)]
        rw [Nat.add_sub_of_le hu]
      · intro b _ hbu
        erw [S.formalMonomial_mul_coeff k]
        split_ifs with hb
        · simp only [formalFactor, PowerSeries.coeff_mk]
          split_ifs with hw hpre
          · have he' : b.val + ⟨v-b.val.val,hw⟩ = ⟨v,hv⟩ := by
              apply Subtype.ext; change b.val.val+(v-b.val.val)=v; omega
            rw [he'] at hpre
            exact (hbu (Subtype.ext hpre.symm)).elim
          · rfl
          · rfl
        · rfl
      · simp
    · rw [hf ⟨v,hv⟩ (show S.order v < n by omega)]
      symm
      apply Finset.sum_eq_zero
      intro b _
      erw [S.formalMonomial_mul_coeff k]
      split_ifs with hb
      · simp only [formalFactor, PowerSeries.coeff_mk]
        split_ifs with hw hpre
        · have he' : b.val + ⟨v-b.val.val,hw⟩ = ⟨v,hv⟩ := by
            apply Subtype.ext; change b.val.val+(v-b.val.val)=v; omega
          have ht := S.order_add b.val.property hw
          have hv' : b.val.val + (v-b.val.val) = v := by omega
          rw [hv', b.property] at ht
          omega
        · rfl
        · rfl
      · rfl
  · rw [f.property v hv]
    symm
    apply Finset.sum_eq_zero
    intro b _
    exact (S.formalMonomial k b.val 1 * S.formalFactor k n f b).property v hv

/-- Actual ideal powers equal the order condition, including infinite series. -/
theorem formalOrderIdeal_eq_pow (n : ℕ) :
    S.formalOrderIdeal k n = S.formalMaximalIdeal k ^ n := by
  apply le_antisymm _ (S.formalMaximalIdeal_pow_le k n)
  intro f hf
  rw [S.formal_order_factorization k n f hf]
  apply Ideal.sum_mem
  intro u _
  exact (S.formalMaximalIdeal k ^ n).mul_mem_right _
    (Ideal.pow_le_pow_right (le_of_eq u.property.symm) (S.formalMonomial_order_mem_pow k u.val))

theorem mem_formalMaximalIdeal_pow (n : ℕ) (f : S.FormalSemigroupRing k) :
    f ∈ S.formalMaximalIdeal k ^ n ↔
      ∀ x : S.carrier, S.order x.val < n → PowerSeries.coeff x.val f.val = 0 := by
  rw [← S.formalOrderIdeal_eq_pow]
  rfl

end NSP14.NumericalSemigroup
