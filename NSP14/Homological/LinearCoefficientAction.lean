module
public import NSP14.Homological.LinearVariables
public import NSP14.Homological.RestrictedScalars
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped BigOperators Classical
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ] (M : ModuleCat.{u} (VariableRing k σ))

theorem linearPolynomial_coefficient_smul (c : σ → k) (a : coefficientModule k σ M) :
    linearPolynomial k σ c • a=∑ i,c i • ((MvPolynomial.X i : VariableRing k σ) • a) := by
  change linearPolynomial k σ c • (show M from a)=
    ∑ i,(algebraMap k (VariableRing k σ) (c i)) • ((MvPolynomial.X i : VariableRing k σ) • (show M from a))
  rw [linearPolynomial_apply,Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Algebra.smul_def,mul_smul]
end NSP14.Homological
