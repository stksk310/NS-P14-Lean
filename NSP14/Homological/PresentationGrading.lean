module

public import NSP14.Homological.Presentation
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

open scoped BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

theorem tangent_one_mem_degree_zero : (1 : S.TangentAlgebra k) ∈ S.tangentDegree k 0 := by
  rw [← S.initialMonomial_zero k]
  exact S.initialMonomial_mem_tangentDegree k 0 0 (S.order_zero)

theorem tangentDegree_pow_mem {a : S.TangentAlgebra k} {d : ℕ}
    (ha : a ∈ S.tangentDegree k d) (n : ℕ) : a^n ∈ S.tangentDegree k (d*n) := by
  induction n with
  | zero => simpa using S.tangent_one_mem_degree_zero k
  | succ n ih =>
    simpa [pow_succ,Nat.mul_succ] using S.tangentDegree_mul_mem k ih ha

theorem tangentDegree_prod_mem {ι : Type*} (s : Finset ι) (a : ι → S.TangentAlgebra k)
    (d : ι → ℕ) (ha : ∀ i∈s, a i∈S.tangentDegree k (d i)) :
    ∏ i∈s,a i ∈ S.tangentDegree k (∑ i∈s,d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S.tangent_one_mem_degree_zero k
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    exact S.tangentDegree_mul_mem k (ha i (Finset.mem_insert_self _ _))
      (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj)))

theorem fullPolynomialToG_monomial_degree (d : S.AtomExponent →₀ ℕ) (c : k) :
    S.fullPolynomialToG k (MvPolynomial.monomial d c) ∈ S.tangentDegree k d.degree := by
  classical
  rw [MvPolynomial.monomial_eq,map_mul]
  change (S.fullPolynomialToG k (MvPolynomial.C c)) *
    S.fullPolynomialToG k (∏ x∈d.support, MvPolynomial.X x ^ d x) ∈ _
  rw [map_prod]
  have hc : S.fullPolynomialToG k (MvPolynomial.C c)=algebraMap k (S.TangentAlgebra k) c :=
    (S.fullPolynomialToG k).commutes c
  rw [hc,← Algebra.smul_def]
  apply (S.tangentDegree k d.degree).smul_mem
  have hp := S.tangentDegree_prod_mem k d.support
    (fun x => S.fullPolynomialToG k (MvPolynomial.X x)^d x) (fun x => d x) (fun x _ => by
      have hx : S.fullPolynomialToG k (MvPolynomial.X x)∈S.tangentDegree k 1 := by
        rw [S.fullPolynomialToG_X]
        exact S.initialMonomial_mem_tangentDegree k 1 x.val (S.atom_order x.property)
      simpa using S.tangentDegree_pow_mem k hx (d x))
  simpa only [map_pow,Finsupp.degree_apply] using hp

/-- Full presentation respects every homogeneous polynomial piece, not only its variables. -/
theorem fullPolynomialToG_homogeneous (p : S.FullPolynomialRing k) (n : ℕ)
    (hp : p.IsHomogeneous n) : S.fullPolynomialToG k p ∈ S.tangentDegree k n := by
  classical
  rw [MvPolynomial.as_sum p,map_sum]
  apply (S.tangentDegree k n).sum_mem
  intro d hd
  have he : d.degree=n := by
    have hh : p ∈ MvPolynomial.homogeneousSubmodule S.AtomExponent k n := hp
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported] at hh
    exact ((Finsupp.mem_supported k _).mp hh) hd
  rw [← he]
  exact S.fullPolynomialToG_monomial_degree k d _

end NSP14.NumericalSemigroup
