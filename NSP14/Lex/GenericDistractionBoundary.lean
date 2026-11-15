module
public import NSP14.Lex.GenericDistractionExterior
public import NSP14.Homological.LinearCoefficientAction
@[expose] public section
open scoped Classical BigOperators TensorProduct
open CategoryTheory NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
local notation "K" => GenericDistractionField k q

theorem genericFieldLinear_sum (a : Fin q →₀ ℕ) (i : Fin q) :
    genericFieldLinear k q i (a i)=
      ∑ r : Fin q,genericFieldMatrix k q a r i • (MvPolynomial.X r : VariableRing K (Fin q)) := by
  rw [← variableLinearCombination_generic k q a i]
  change (∑ r,(genericFieldLinearEquiv k q a (Pi.single i 1)) r • MvPolynomial.X r)=_
  simp_rw [genericFieldLinearEquiv_single]

theorem genericFieldLinear_smul (M : ModuleCat (VariableRing K (Fin q)))
    (a : Fin q →₀ ℕ) (i : Fin q) (m : coefficientModule K (Fin q) M) :
    genericFieldLinear k q i (a i) • m =
      ∑ r : Fin q,genericFieldMatrix k q a r i • ((MvPolynomial.X r : VariableRing K (Fin q)) • m) := by
  have he : genericFieldLinear k q i (a i)=
      linearPolynomial K (Fin q) (fun r => genericFieldMatrix k q a r i) :=
    genericFieldLinear_sum k q a i
  rw [he]
  exact linearPolynomial_coefficient_smul K (Fin q) M _ m

theorem genericFieldDistraction_step_smul (M : ModuleCat (VariableRing K (Fin q)))
    (a : Fin q →₀ ℕ) (i : Fin q) (m : coefficientModule K (Fin q) M) :
    genericFieldDistraction k q (a+Finsupp.single i 1) • m =
      ∑ r : Fin q,genericFieldMatrix k q a r i •
        ((MvPolynomial.X r : VariableRing K (Fin q)) • (genericFieldDistraction k q a • m)) := by
  rw [genericFieldDistraction_step,mul_smul,genericFieldLinear_smul]

theorem genericDistractionContraction_row (j : ℕ) (a : Fin q →₀ ℕ) (r : Fin q)
    (w : ⋀[K]^(j+1) (Fin q → K)) :
    koszulExteriorContraction K (Fin q) j
      ((LinearMap.proj r : (Fin q → K) →ₗ[K] K).comp (genericFieldLinearEquiv k q a).toLinearMap) w =
      ∑ i : Fin q, genericFieldMatrix k q a r i • koszulExteriorContraction K (Fin q) j (LinearMap.proj i) w := by
  rw [koszulExteriorContraction_decompose]
  apply Finset.sum_congr rfl
  intro i _
  have he : ((LinearMap.proj r : (Fin q → K) →ₗ[K] K).comp
      (genericFieldLinearEquiv k q a).toLinearMap) (Pi.single i 1)=genericFieldMatrix k q a r i := by
    simp only [LinearMap.comp_apply,LinearMap.proj_apply,LinearEquiv.coe_coe]
    exact genericFieldLinearEquiv_single k q a i r
  congr 1
  convert he using 1
  congr 1
  funext x
  by_cases hx : x=i <;> simp only [Pi.single_apply,hx,ite_true,ite_false]

theorem genericDistractionBoundary_monomial (M : ModuleCat (VariableRing K (Fin q))) {J : Type}
    (b : Module.Basis J K (coefficientModule K (Fin q) M)) (j : ℕ) (a : Fin q →₀ ℕ)
    (m : coefficientModule K (Fin q) M) (w : ⋀[K]^(j+1) (Fin q → K)) :
    koszulExteriorBoundary K (Fin q) M b j
      ((genericFieldDistraction k q a • m) ⊗ₜ[K] genericDistractionWedgeEquiv k q (j+1) a w)=
      ∑ i : Fin q, (genericFieldDistraction k q (a+Finsupp.single i 1) • m) ⊗ₜ[K]
        genericDistractionWedgeEquiv k q j (a+Finsupp.single i 1)
          (koszulExteriorContraction K (Fin q) j (LinearMap.proj i) w) := by
  rw [koszulExteriorBoundary_tmul]
  simp_rw [genericDistractionWedge_contraction,genericDistractionContraction_row,map_sum,map_smul,
    TensorProduct.tmul_sum,TensorProduct.tmul_smul]
  simp_rw [← genericDistractionWedge_step_contraction k q j a,
    genericFieldDistraction_step_smul,TensorProduct.sum_tmul]
  rw [Finset.sum_comm]
  rfl
end NSP14.Lex
