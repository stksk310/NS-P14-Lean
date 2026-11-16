module

public import NSP14.Homological.PolynomialBaseChangeFunctor

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k]
variable {M N : ModuleCat.{u} (VariableRing k σ)}

/-- A coefficient-linear map commuting with the actual variables is polynomial-linear. -/
theorem polynomialLinear_of_variable_commutes
    (f : coefficientModule k σ M →ₗ[k] coefficientModule k σ N)
    (hf : ∀ (x : σ) a,f ((MvPolynomial.X x : VariableRing k σ) • a)=
      (MvPolynomial.X x : VariableRing k σ) • f a)
    (p : VariableRing k σ) (a : coefficientModule k σ M) : f (p • a)=p • f a := by
  induction p using MvPolynomial.induction_on generalizing a with
  | C c =>
    change f ((algebraMap k (VariableRing k σ) c) • a)=
      (algebraMap k (VariableRing k σ) c) • f a
    rw [algebraMap_smul,algebraMap_smul,f.map_smul]
  | add p q hp hq => simp only [add_smul,map_add,hp,hq]
  | mul_X p x hp => rw [mul_smul,hp,hf,mul_smul]

noncomputable def polynomialHomOfVariables
    (f : coefficientModule k σ M →ₗ[k] coefficientModule k σ N)
    (hf : ∀ (x : σ) a,f ((MvPolynomial.X x : VariableRing k σ) • a)=
      (MvPolynomial.X x : VariableRing k σ) • f a) : M ⟶ N :=
  ModuleCat.ofHom (X := M) (Y := N) {
    toFun := f
    map_add' := f.map_add
    map_smul' := polynomialLinear_of_variable_commutes k σ f hf }

end NSP14.Homological
