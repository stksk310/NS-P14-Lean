module

public import NSP14.Semigroup.LiveSplit
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.Ideal.Maps

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

/-- The literal formal-series model k[[S]]: all power series supported on actual S. -/
noncomputable def formalSeriesAlgebra : Subalgebra k (PowerSeries k) where
  carrier := {f | ∀ n, n ∉ S → PowerSeries.coeff n f = 0}
  zero_mem' := by intro n _; simp
  one_mem' := by
    intro n hn
    have hn0 : n ≠ 0 := by intro h; exact hn (h ▸ S.zero_mem)
    simp [PowerSeries.coeff_one, hn0]
  add_mem' := by
    intro f g hf hg n hn
    rw [map_add, hf n hn, hg n hn, zero_add]
  mul_mem' := by
    intro f g hf hg n hn
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have heq := Finset.mem_antidiagonal.mp hp
    by_cases hleft : p.1 ∈ S
    · have hright : p.2 ∉ S := by intro hr; exact hn (heq ▸ S.add_mem hleft hr)
      rw [hg p.2 hright, mul_zero]
    · rw [hf p.1 hleft, zero_mul]
  algebraMap_mem' := by
    intro c n hn
    have hn0 : n ≠ 0 := by intro h; exact hn (h ▸ S.zero_mem)
    change PowerSeries.coeff n (PowerSeries.C c) = 0
    simp [PowerSeries.coeff_C, hn0]

abbrev FormalSemigroupRing := ↥(S.formalSeriesAlgebra k)

noncomputable instance formalSemigroupCommRing : CommRing (S.FormalSemigroupRing k) :=
  (S.formalSeriesAlgebra k).toCommRing

noncomputable instance formalSemigroupAlgebra : Algebra k (S.FormalSemigroupRing k) :=
  (S.formalSeriesAlgebra k).algebra

noncomputable def formalMonomial (x : S.carrier) (c : k) : S.FormalSemigroupRing k :=
  ⟨PowerSeries.monomial x.val c, by
    intro n hn
    have hne : n ≠ x.val := by intro he; exact hn (he.symm ▸ x.property)
    simp [PowerSeries.coeff_monomial, hne]⟩

theorem formalMonomial_coeff (x : S.carrier) (c : k) (n : ℕ) :
    PowerSeries.coeff n (S.formalMonomial k x c).val = if n = x.val then c else 0 := by
  exact PowerSeries.coeff_monomial n x.val c

theorem formalMonomial_mul (x y : S.carrier) (c d : k) :
    S.formalMonomial k x c * S.formalMonomial k y d = S.formalMonomial k (x + y) (c*d) := by
  apply Subtype.ext
  exact PowerSeries.monomial_mul_monomial _ _ _ _

noncomputable def formalConstantCoeff : S.FormalSemigroupRing k →+* k :=
  PowerSeries.constantCoeff.comp (S.formalSeriesAlgebra k).val.toRingHom

noncomputable def formalMaximalIdeal : Ideal (S.FormalSemigroupRing k) :=
  RingHom.ker (S.formalConstantCoeff k)

theorem formalConstantCoeff_surjective : Function.Surjective (S.formalConstantCoeff k) := by
  intro c
  refine ⟨S.formalMonomial k 0 c, ?_⟩
  change PowerSeries.constantCoeff (PowerSeries.monomial (0 : ℕ) c) = c
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

theorem formalMaximalIdeal_isMaximal (K : Type*) [Field K] : (S.formalMaximalIdeal K).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (S.formalConstantCoeff_surjective K)

end NSP14.NumericalSemigroup
