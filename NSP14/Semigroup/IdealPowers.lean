module

public import NSP14.Semigroup.Ring

@[expose] public section

open scoped BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

theorem positive_single_mem (x : S.carrier) (hx : 0 < x.val) :
    AddMonoidAlgebra.single x (1 : k) ∈ S.positiveIdeal k := by
  rw [← S.orderIdeal_one k]
  exact S.single_mem_orderIdeal k 1 x 1 (S.order_pos x.property hx)

theorem single_sum_mem_pow (n : ℕ) (f : Fin n → S.carrier)
    (hf : ∀ i, 0 < (f i).val) :
    AddMonoidAlgebra.single (∑ i, f i) (1 : k) ∈ S.positiveIdeal k ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ht := ih (fun i => f i.succ) (fun i => hf i.succ)
    have hh := S.positive_single_mem k (f 0) (hf 0)
    have hm := Ideal.mul_mem_mul ht hh
    simpa [pow_succ, AddMonoidAlgebra.single_mul_single, Fin.sum_univ_succ, add_comm]
      using hm

theorem single_order_mem_pow (x : S.carrier) :
    AddMonoidAlgebra.single x (1 : k) ∈ S.positiveIdeal k ^ S.order x.val := by
  obtain ⟨f, hf, heq⟩ := S.order_length x.property
  let g : Fin (S.order x.val) → S.carrier := fun i => ⟨f i, (hf i).1⟩
  have hg : ∑ i, g i = x := by
    apply Subtype.ext
    simpa [g] using heq
  simpa [hg] using S.single_sum_mem_pow k _ g (fun i => (hf i).2)

theorem positiveIdeal_pow_le (n : ℕ) : S.positiveIdeal k ^ n ≤ S.orderIdeal k n := by
  induction n with
  | zero => simp [S.orderIdeal_zero k]
  | succ n ih =>
    rw [pow_succ]
    exact (Ideal.mul_mono ih (le_of_eq (S.orderIdeal_one k).symm)).trans
      (S.orderIdeal_mul_le k n 1)

/-- Numerical order is exactly the monomial membership filtration of the actual ideal. -/
theorem orderIdeal_eq_pow (n : ℕ) : S.orderIdeal k n = S.positiveIdeal k ^ n := by
  apply le_antisymm _ (S.positiveIdeal_pow_le k n)
  intro f hf
  apply S.mem_of_support_single_mem k _ f
  intro x hx
  have hn := (S.mem_orderIdeal_iff k n f).1 hf x hx
  have hm := Ideal.pow_le_pow_right hn (S.single_order_mem_pow k x)
  have := (S.positiveIdeal k ^ n).mul_mem_left
    (AddMonoidAlgebra.single (0 : S.carrier) (f.coeff x)) hm
  simpa using this

theorem mem_positiveIdeal_pow (n : ℕ) (f : S.SemigroupRing k) :
    f ∈ S.positiveIdeal k ^ n ↔ ∀ x, S.order x.val < n → f.coeff x = 0 := by
  rw [← S.orderIdeal_eq_pow k n, S.mem_orderIdeal_coeff]

theorem monomial_mem_pow_iff [Nontrivial k] (n : ℕ) (x : S.carrier) :
    AddMonoidAlgebra.single x (1 : k) ∈ S.positiveIdeal k ^ n ↔ n ≤ S.order x.val := by
  rw [← S.orderIdeal_eq_pow k n, S.single_mem_orderIdeal_iff]

theorem mem_positiveIdeal (f : S.SemigroupRing k) :
    f ∈ S.positiveIdeal k ↔ f.coeff 0 = 0 := by
  rw [← pow_one (S.positiveIdeal k), S.mem_positiveIdeal_pow]
  constructor
  · intro h
    exact h 0 (by simp [S.order_zero])
  · intro h x hx
    have hz : S.order x.val = 0 := by omega
    have hv := (S.order_eq_zero_iff x.property).1 hz
    have heq : x = 0 := Subtype.ext hv
    simpa [heq] using h

end NSP14.NumericalSemigroup
