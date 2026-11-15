module
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Lex
variable (R : Type) [CommRing R] (q : ℕ)

noncomputable def distractionMonomial (L : Fin q → ℕ → MvPolynomial (Fin q) R) (a : Fin q →₀ ℕ) :
    MvPolynomial (Fin q) R := ∏ i,∏ j ∈ Finset.range (a i),L i j

theorem distractionMonomial_zero (L : Fin q → ℕ → MvPolynomial (Fin q) R) :
    distractionMonomial R q L 0=1 := by simp [distractionMonomial]

theorem distractionMonomial_step (L : Fin q → ℕ → MvPolynomial (Fin q) R) (a : Fin q →₀ ℕ) (i : Fin q) :
    distractionMonomial R q L (a+Finsupp.single i 1)=L i (a i)*distractionMonomial R q L a := by
  have he (x : Fin q) : (∏ j ∈ Finset.range ((a+Finsupp.single i 1 : Fin q →₀ ℕ) x),L x j)=
      (if x=i then L i (a i) else 1)*(∏ j ∈ Finset.range (a x),L x j) := by
    by_cases hx : x=i
    · subst x
      simp only [Finsupp.add_apply,Finsupp.single_eq_same,ite_true,Finset.prod_range_succ,mul_comm]
    · simp only [Finsupp.add_apply,Finsupp.single_eq_of_ne hx,Nat.add_zero,ite_eq_right hx,one_mul]
  calc
    distractionMonomial R q L (a+Finsupp.single i 1)=
        ∏ x,(if x=i then L i (a i) else 1)*(∏ j ∈ Finset.range (a x),L x j) :=
      Finset.prod_congr rfl (fun x _ => he x)
    _=(∏ x : Fin q,if x=i then L i (a i) else 1)*distractionMonomial R q L a := by
      rw [Finset.prod_mul_distrib]
      rfl
    _=L i (a i)*distractionMonomial R q L a := by simp

theorem distractionMonomial_homogeneous (L : Fin q → ℕ → MvPolynomial (Fin q) R)
    (hL : ∀ i j,(L i j).IsHomogeneous 1) (a : Fin q →₀ ℕ) :
    (distractionMonomial R q L a).IsHomogeneous a.degree := by
  rw [Finsupp.degree_eq_sum]
  apply MvPolynomial.IsHomogeneous.prod
  intro i _
  have h := MvPolynomial.IsHomogeneous.prod (Finset.range (a i)) (L i) (fun _ => 1) (fun j _ => hL i j)
  simpa only [Finset.sum_const,Finset.card_range,smul_eq_mul,mul_one] using h

theorem distractionMonomial_variables (a : Fin q →₀ ℕ) :
    distractionMonomial R q (fun i _ => MvPolynomial.X i) a=MvPolynomial.monomial a 1 := by
  unfold distractionMonomial
  simp only [Finset.prod_const,Finset.card_range]
  rw [←MvPolynomial.prod_X_pow_eq_monomial]
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have ha : a i=0 := Finsupp.notMem_support_iff.mp hi
  simp only [ha,pow_zero]
end NSP14.Lex
