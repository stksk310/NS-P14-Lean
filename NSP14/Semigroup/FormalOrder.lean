module

public import NSP14.Semigroup.FormalSemigroupRing
public import NSP14.Semigroup.GradedBasis

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

/-- A coefficient condition, initially distinct from the powers of the maximal ideal. -/
noncomputable def formalOrderIdeal (n : ℕ) : Ideal (S.FormalSemigroupRing k) where
  carrier := {f | ∀ x : S.carrier, S.order x.val < n → PowerSeries.coeff x.val f.val = 0}
  zero_mem' := by intro x _; simp
  add_mem' := by
    intro f g hf hg x hx
    change PowerSeries.coeff x.val (f.val + g.val) = 0
    rw [map_add, hf x hx, hg x hx, zero_add]
  smul_mem' r f hf := by
    intro x hx
    change PowerSeries.coeff x.val (r.val * f.val) = 0
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have heq := Finset.mem_antidiagonal.mp hp
    by_cases hr : p.1 ∈ S
    · by_cases hff : p.2 ∈ S
      · have ho := S.order_add hr hff
        rw [heq] at ho
        rw [hf ⟨p.2,hff⟩ (show S.order p.2 < n by omega), mul_zero]
      · rw [f.property p.2 hff, mul_zero]
    · rw [r.property p.1 hr, zero_mul]

theorem mem_formalOrderIdeal (n : ℕ) (f : S.FormalSemigroupRing k) :
    f ∈ S.formalOrderIdeal k n ↔
      ∀ x : S.carrier, S.order x.val < n → PowerSeries.coeff x.val f.val = 0 := Iff.rfl

theorem formalOrderIdeal_zero : S.formalOrderIdeal k 0 = ⊤ := by
  ext f
  simp only [S.mem_formalOrderIdeal, Submodule.mem_top, iff_true]
  intro x hx
  omega

theorem formalOrderIdeal_one : S.formalOrderIdeal k 1 = S.formalMaximalIdeal k := by
  ext f
  change (∀ x : S.carrier, S.order x.val < 1 → PowerSeries.coeff x.val f.val = 0) ↔
    PowerSeries.constantCoeff f.val = 0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  constructor
  · intro h
    exact h 0 (by simp [S.order_zero])
  · intro h x hx
    have hv := (S.order_eq_zero_iff x.property).1 (by omega : S.order x.val = 0)
    simpa [hv] using h

theorem formalOrderIdeal_mul_le (n p : ℕ) :
    S.formalOrderIdeal k n * S.formalOrderIdeal k p ≤ S.formalOrderIdeal k (n+p) := by
  apply Ideal.mul_le.mpr
  intro f hf g hg x hx
  change PowerSeries.coeff x.val (f.val*g.val) = 0
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro a ha
  have heq := Finset.mem_antidiagonal.mp ha
  by_cases h1 : a.1 ∈ S
  · by_cases h2 : a.2 ∈ S
    · have ho := S.order_add h1 h2
      rw [heq] at ho
      by_cases hl : S.order a.1 < n
      · rw [hf ⟨a.1,h1⟩ hl, zero_mul]
      · rw [hg ⟨a.2,h2⟩ (show S.order a.2 < p by omega), mul_zero]
    · rw [g.property a.2 h2, mul_zero]
  · rw [f.property a.1 h1, zero_mul]

theorem formalMaximalIdeal_pow_le (n : ℕ) :
    S.formalMaximalIdeal k ^ n ≤ S.formalOrderIdeal k n := by
  induction n with
  | zero => simp [S.formalOrderIdeal_zero k]
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (le_of_eq (S.formalOrderIdeal_one k).symm)).trans
      (S.formalOrderIdeal_mul_le k n 1)

theorem formalMonomial_mem_orderIdeal (n : ℕ) (x : S.carrier) (c : k)
    (h : n ≤ S.order x.val) : S.formalMonomial k x c ∈ S.formalOrderIdeal k n := by
  intro y hy
  rw [S.formalMonomial_coeff]
  have hn : y.val ≠ x.val := by intro he; rw [he] at hy; omega
  simp [hn]

theorem formalMonomial_zero_one : S.formalMonomial k 0 1 = 1 := by
  apply Subtype.ext
  change PowerSeries.monomial 0 (1 : k) = 1
  simp [PowerSeries.monomial_zero_eq_C_apply]

theorem formalMonomial_sum (n : ℕ) (f : Fin n → S.carrier) :
    S.formalMonomial k (∑ i, f i) 1 = ∏ i, S.formalMonomial k (f i) 1 := by
  induction n with
  | zero => simp [S.formalMonomial_zero_one k]
  | succ n ih =>
    rw [Fin.sum_univ_succ, Fin.prod_univ_succ, ← ih, S.formalMonomial_mul, one_mul]

theorem formalMonomial_order_mem_pow (x : S.carrier) :
    S.formalMonomial k x 1 ∈ S.formalMaximalIdeal k ^ S.order x.val := by
  obtain ⟨f,hf,heq⟩ := S.order_length x.property
  let g : Fin (S.order x.val) → S.carrier := fun i => ⟨f i,(hf i).1⟩
  have he : ∑ i, g i = x := by apply Subtype.ext; simpa [g] using heq
  have hp : (∏ i, S.formalMonomial k (g i) 1) ∈
      ∏ _i : Fin (S.order x.val), S.formalMaximalIdeal k := by
    apply Ideal.prod_mem_prod
    intro i _
    rw [← S.formalOrderIdeal_one k]
    exact S.formalMonomial_mem_orderIdeal k 1 (g i) 1 (S.order_pos (g i).property (hf i).2)
  simpa only [← S.formalMonomial_sum k, he, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] using hp

end NSP14.NumericalSemigroup
