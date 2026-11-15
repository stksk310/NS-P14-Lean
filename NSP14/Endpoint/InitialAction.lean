module
public import NSP14.Homological.NormalTriangular
public import NSP14.Lex.InitialIdeal
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
namespace NSP14.Endpoint
variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))

/-- Actual quotient-variable multiplication is the normal form of the
corresponding actual monomial product, in the same standard basis. -/
theorem artin_variable_normal (x : Fin q)
    (p j : StandardExponent MonomialOrder.degLex I) :
    artinCoordinates k (Fin q) I ((MvPolynomial.X x : VariableRing k (Fin q)) •
      (artinCoordinates k (Fin q) I).symm (Finsupp.single p 1)) j=
    (actualNormalForm k MonomialOrder.degLex I
      (MvPolynomial.monomial (p.val+Finsupp.single x 1) 1)).coeff j.val := by
  rw [artinCoordinates_single]
  change (actualNormalForm k MonomialOrder.degLex I
    (MvPolynomial.X x*MvPolynomial.monomial p.val 1)).coeff j.val=_
  simp only [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul,add_comm]

theorem artin_variable_triangular (x : Fin q)
    (p j : StandardExponent MonomialOrder.degLex I)
    (h : MonomialOrder.degLex.toSyn (p.val+Finsupp.single x 1) < MonomialOrder.degLex.toSyn j.val) :
    artinCoordinates k (Fin q) I ((MvPolynomial.X x : VariableRing k (Fin q)) •
      (artinCoordinates k (Fin q) I).symm (Finsupp.single p 1)) j=0 := by
  rw [artin_variable_normal]
  apply actualNormalForm_coeff_zero_above k MonomialOrder.degLex I
  simpa only [MonomialOrder.degree_monomial,ite_eq_right one_ne_zero] using h

/-- When the product survives, the actual action is its unit coordinate. -/
theorem artin_variable_standard (x : Fin q)
    (p j : StandardExponent MonomialOrder.degLex I)
    (h : p.val+Finsupp.single x 1 ∈ StandardExponent MonomialOrder.degLex I) :
    artinCoordinates k (Fin q) I ((MvPolynomial.X x : VariableRing k (Fin q)) •
      (artinCoordinates k (Fin q) I).symm (Finsupp.single p 1)) j=
      if p.val+Finsupp.single x 1=j.val then 1 else 0 := by
  rw [artin_variable_normal,actualNormalForm_monomial k MonomialOrder.degLex I _ h]
  exact MvPolynomial.coeff_monomial _ _ _

/-- A killed leading monomial contributes zero throughout its own and
higher ordered blocks, without asserting its actual action is zero. -/
theorem artin_variable_nonstandard (x : Fin q)
    (p j : StandardExponent MonomialOrder.degLex I)
    (h : p.val+Finsupp.single x 1 ∉ StandardExponent MonomialOrder.degLex I)
    (hle : MonomialOrder.degLex.toSyn (p.val+Finsupp.single x 1) ≤ MonomialOrder.degLex.toSyn j.val) :
    artinCoordinates k (Fin q) I ((MvPolynomial.X x : VariableRing k (Fin q)) •
      (artinCoordinates k (Fin q) I).symm (Finsupp.single p 1)) j=0 := by
  rw [artin_variable_normal]
  exact actualNormalForm_coeff_zero_ge_nonstandard k MonomialOrder.degLex I _ h _ hle
/-- In an actual monomial quotient, variable multiplication has only its
literal surviving monomial coordinate. -/
theorem artin_variable_monomial (hI : Lex.IsMonomial k q I) (x : Fin q)
    (p j : StandardExponent MonomialOrder.degLex I) :
    artinCoordinates k (Fin q) I ((MvPolynomial.X x : VariableRing k (Fin q)) •
      (artinCoordinates k (Fin q) I).symm (Finsupp.single p 1)) j=
      if p.val+Finsupp.single x 1=j.val then 1 else 0 := by
  by_cases hs : p.val+Finsupp.single x 1 ∈ StandardExponent MonomialOrder.degLex I
  · exact artin_variable_standard k q I x p j hs
  · have hm : MvPolynomial.monomial (p.val+Finsupp.single x 1) (1:k) ∈ I := by
      simpa only [Lex.standardExponent_iff_not_mem k q hI,not_not] using hs
    have hn : p.val+Finsupp.single x 1 ≠ j.val := fun he => hs (he ▸ j.property)
    rw [artin_variable_normal,actualNormalForm_of_mem k MonomialOrder.degLex I _ hm]
    simp only [AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,ite_eq_right hn]
end NSP14.Endpoint
