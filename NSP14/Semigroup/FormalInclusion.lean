module

public import NSP14.Semigroup.FormalTangentAlgebra
public import NSP14.Semigroup.TangentScalars
public import Mathlib.Algebra.MonoidAlgebra.Basic

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

noncomputable def formalMonomialHom : Multiplicative S.carrier →* S.FormalSemigroupRing k where
  toFun x := S.formalMonomial k x.toAdd 1
  map_one' := S.formalMonomial_zero_one k
  map_mul' x y := by
    change S.formalMonomial k (x.toAdd+y.toAdd) 1 = _
    rw [S.formalMonomial_mul, one_mul]

/-- The natural inclusion of finite semigroup polynomials into actual formal series. -/
noncomputable def polynomialToFormal : S.SemigroupRing k →ₐ[k] S.FormalSemigroupRing k :=
  AddMonoidAlgebra.lift k (S.FormalSemigroupRing k) S.carrier (S.formalMonomialHom k)

theorem polynomialToFormal_single (x : S.carrier) (c : k) :
    S.polynomialToFormal k (AddMonoidAlgebra.single x c) = S.formalMonomial k x c := by
  rw [polynomialToFormal, AddMonoidAlgebra.lift_single]
  apply Subtype.ext
  change c • PowerSeries.monomial x.val 1 = PowerSeries.monomial x.val c
  rw [← map_smul, smul_eq_mul, mul_one]

theorem polynomialToFormal_coeff (f : S.SemigroupRing k) (x : S.carrier) :
    PowerSeries.coeff x.val (S.polynomialToFormal k f).val = f.coeff x := by
  induction f using AddMonoidAlgebra.induction_on with
  | of y =>
    change PowerSeries.coeff x.val (S.polynomialToFormal k (AddMonoidAlgebra.single y 1)).val = _
    rw [S.polynomialToFormal_single, S.formalMonomial_coeff]
    change (if x.val=y.val then (1:k) else 0) = Finsupp.single y 1 x
    by_cases h : x = y
    · subst y; simp
    · have hv : x.val ≠ y.val := fun he => h (Subtype.ext he)
      simp [hv, Ne.symm h]
  | add f g hf hg =>
    rw [map_add]
    change PowerSeries.coeff x.val ((S.polynomialToFormal k f).val +
      (S.polynomialToFormal k g).val) = f.coeff x + g.coeff x
    rw [map_add, hf, hg]
  | smul c f hf =>
    rw [map_smul]
    change PowerSeries.coeff x.val (c • (S.polynomialToFormal k f).val) = c • f.coeff x
    rw [map_smul, hf]

theorem polynomialToFormal_mem_pow (n : ℕ) (f : S.SemigroupRing k) :
    S.polynomialToFormal k f ∈ S.formalMaximalIdeal k ^ n ↔ f ∈ S.positiveIdeal k ^ n := by
  rw [S.mem_formalMaximalIdeal_pow, S.mem_positiveIdeal_pow]
  simp only [S.polynomialToFormal_coeff]

noncomputable def formalTruncation (n : ℕ) (f : S.FormalSemigroupRing k) : S.SemigroupRing k :=
  ∑ u : S.DegreeExponent n, AddMonoidAlgebra.single u.val (PowerSeries.coeff u.val.val f.val)

theorem formalTruncation_coeff (n : ℕ) (f : S.FormalSemigroupRing k) (x : S.carrier) :
    (S.formalTruncation k n f).coeff x =
      if S.order x.val = n then PowerSeries.coeff x.val f.val else 0 := by
  let : Fintype {x : S.carrier // S.order x.val = n} := S.degreeExponentFintype n
  rw [formalTruncation, AddMonoidAlgebra.coeff_sum, Finset.sum_apply']
  by_cases hx : S.order x.val = n
  · erw [Finset.sum_eq_single (⟨x,hx⟩ : S.DegreeExponent n)]
    · simp [hx]
    · intro b _ hb
      have hne : b.val ≠ x := fun h => hb (Subtype.ext h)
      simp [hne]
    · intro hm; exact (hm (Finset.mem_univ (⟨x,hx⟩ : S.DegreeExponent n))).elim
  · rw [ite_eq_right_iff.mpr (fun h => (hx h).elim)]
    apply Finset.sum_eq_zero
    intro b _
    have hne : b.val ≠ x := by intro he; exact hx (he ▸ b.property)
    simp [hne]

theorem formalTruncation_mem (n : ℕ) (f : S.FormalSemigroupRing k) :
    S.formalTruncation k n f ∈ S.positiveIdeal k ^ n := by
  rw [S.mem_positiveIdeal_pow]
  intro x hx
  rw [S.formalTruncation_coeff]
  have hn : S.order x.val ≠ n := by omega
  simp [hn]

theorem formalTruncation_difference (n : ℕ) (f : S.FormalSemigroupRing k)
    (hf : f ∈ S.formalMaximalIdeal k ^ n) :
    f - S.polynomialToFormal k (S.formalTruncation k n f) ∈ S.formalMaximalIdeal k ^ (n+1) := by
  rw [S.mem_formalMaximalIdeal_pow]
  intro x hx
  change PowerSeries.coeff x.val (f.val-(S.polynomialToFormal k (S.formalTruncation k n f)).val) = 0
  rw [map_sub, S.polynomialToFormal_coeff, S.formalTruncation_coeff]
  by_cases hn : S.order x.val=n
  · simp [hn]
  · have hz := (S.mem_formalMaximalIdeal_pow k n f).1 hf x (by omega)
    simp [hn,hz]

end NSP14.NumericalSemigroup
