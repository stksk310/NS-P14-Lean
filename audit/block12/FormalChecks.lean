module
import NSP14
import Mathlib.Data.ZMod.Basic

open NSP14
open scoped Classical BigOperators
noncomputable section
namespace NSP14.Run12Audit

-- The natural inclusion really retains all polynomial coefficients.
theorem polynomial_inclusion_injective (S : NumericalSemigroup) (k : Type*) [CommRing k] :
    Function.Injective (S.polynomialToFormal k) := by
  intro f g h
  apply AddMonoidAlgebra.coeff_injective
  ext x
  have he := congrArg (fun a : S.FormalSemigroupRing k => PowerSeries.coeff x.val a.val) h
  simpa only [S.polynomialToFormal_coeff] using he

private def triple : NumericalSemigroup where
  carrier :=
    { carrier := {n | ∃ a b : ℕ, n=3*a+4*b}
      zero_mem' := ⟨0,0,by omega⟩
      add_mem' := by
        rintro x y ⟨a,b,hx⟩ ⟨c,d,hy⟩
        exact ⟨a+c,b+d,by omega⟩ }
  conductor := 6
  cofinite n hn := by
    have hr := Nat.mod_lt n (by decide : 0<3)
    have he := Nat.mod_add_div n 3
    exact ⟨n/3-n%3,n%3,by omega⟩
private theorem triple_m : triple.multiplicity=3 := by
  apply triple.multiplicity_eq (by decide) (show 3∈triple from ⟨1,0,by omega⟩)
  rintro x ⟨a,b,hx⟩ hp
  have hs : 1≤a+b := by omega
  omega
private theorem triple_order (n : ℕ) : triple.order (3*n)=n := by
  have h3 : 3∈triple := ⟨1,0,by omega⟩
  have hl := triple.length_le_order
    (show triple.HasLength (3*n) n from
      ⟨fun _ => 3,fun _ => ⟨h3,by norm_num⟩,by simp [Nat.mul_comm]⟩)
  have hh := triple.order_bound (show 3*n∈triple from ⟨n,0,by omega⟩)
  rw [triple_m] at hh
  omega

-- All coefficients on the infinite ray 3n+3N are one, with no truncation.
private def infiniteRay (k : Type*) [CommRing k] (n : ℕ) : triple.FormalSemigroupRing k :=
  ⟨PowerSeries.mk (fun v => if v%3=0 ∧ 3*n≤v then 1 else 0), by
    intro v hv
    simp only [PowerSeries.coeff_mk]
    split_ifs with h
    · exfalso
      apply hv
      have he := Nat.mod_add_div v 3
      exact ⟨v/3,0,by omega⟩
    · rfl⟩

private theorem infiniteRay_coeff (k : Type*) [CommRing k] (n v : ℕ) :
    PowerSeries.coeff v (infiniteRay k n).val = if v%3=0 ∧ 3*n≤v then 1 else 0 := by
  simp only [infiniteRay,PowerSeries.coeff_mk]

private theorem infiniteRay_mem (k : Type*) [CommRing k] (n : ℕ) :
    infiniteRay k n ∈ triple.formalMaximalIdeal k ^ n := by
  rw [triple.mem_formalMaximalIdeal_pow]
  intro x hx
  rw [infiniteRay_coeff]
  split_ifs with h
  · have he := Nat.mod_add_div x.val 3
    have hv : x.val=3*(x.val/3) := by omega
    have ho : triple.order x.val=x.val/3 :=
      (congrArg triple.order hv).trans (triple_order (x.val/3))
    omega
  · rfl

-- Strictness in every degree, including n=0, over any nontrivial coefficient ring.
example (k : Type*) [CommRing k] [Nontrivial k] (n : ℕ) :
    infiniteRay k n ∉ triple.formalMaximalIdeal k ^ (n+1) := by
  intro h
  have hm : 3*n∈triple := ⟨n,0,by omega⟩
  have he := (triple.mem_formalMaximalIdeal_pow k (n+1) _).1 h ⟨3*n,hm⟩
    (by change triple.order (3*n)<n+1; rw [triple_order]; omega)
  rw [infiniteRay_coeff] at he
  have hc : (3*n)%3=0 ∧ 3*n≤3*n := by omega
  simp only [ite_eq_left hc] at he
  exact one_ne_zero he

-- Infinite representatives have actual polynomial lifts modulo the next power.
example (k : Type*) [CommRing k] (n : ℕ) :
    infiniteRay k n - triple.polynomialToFormal k (triple.formalTruncation k n (infiniteRay k n)) ∈
      triple.formalMaximalIdeal k ^ (n+1) :=
  triple.formalTruncation_difference k n (infiniteRay k n) (infiniteRay_mem k n)

example (k : Type*) [CommRing k] (n : ℕ) :
    infiniteRay k n = ∑ u : triple.DegreeExponent n,
      triple.formalMonomial k u.val 1 * triple.formalFactor k n (infiniteRay k n) u :=
  triple.formal_order_factorization k n (infiniteRay k n) (by
    rw [triple.formalOrderIdeal_eq_pow]
    exact infiniteRay_mem k n)

-- Zero coefficients and the zero ring do not require a nontriviality assumption.
example (S : NumericalSemigroup) (a : S.TangentAlgebra (ZMod 1)) :
    S.completedGradedAlgEquiv (ZMod 1) a=0 := Subsingleton.elim _ _
example (k : Type*) [CommRing k] (n : ℕ) (x : triple.carrier) :
    triple.formalMonomial k x 0 ∈ triple.formalMaximalIdeal k ^ n := by
  have hz : triple.formalMonomial k x 0=0 := by
    apply Subtype.ext
    exact map_zero (PowerSeries.monomial x.val)
  rw [hz]
  exact Ideal.zero_mem _

#print axioms polynomial_inclusion_injective
#print axioms infiniteRay_mem
end NSP14.Run12Audit
