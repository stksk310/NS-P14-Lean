module
public import NSP14.Homological.PolynomialEquivBetti
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.AlgebraMap
@[expose] public section
open CategoryTheory
namespace NSP14.Homological
universe u
variable (k τ σ : Type u) [Field k]

noncomputable def optionPolynomialEquiv (e : VariableRing k τ ≃ₐ[k] VariableRing k σ) :
    VariableRing k (Option τ) ≃ₐ[k] VariableRing k (Option σ) :=
  (MvPolynomial.optionEquivLeft k τ).trans ((Polynomial.mapAlgEquiv e).trans (MvPolynomial.optionEquivLeft k σ).symm)

theorem optionPolynomialEquiv_X_none (e : VariableRing k τ ≃ₐ[k] VariableRing k σ) :
    optionPolynomialEquiv k τ σ e (MvPolynomial.X none)=MvPolynomial.X none := by
  simp [optionPolynomialEquiv,Polynomial.coe_mapAlgEquiv]

theorem optionEquivLeft_symm_C (p : VariableRing k σ) :
    (MvPolynomial.optionEquivLeft k σ).symm (Polynomial.C p)=MvPolynomial.rename some p := by
  have h : (MvPolynomial.optionEquivLeft k σ).symm.toAlgHom.comp (Polynomial.CAlgHom (R:=k))=
      (MvPolynomial.rename some : VariableRing k σ →ₐ[k] VariableRing k (Option σ)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,Polynomial.CAlgHom_apply,MvPolynomial.rename_X]
    exact MvPolynomial.optionEquivLeft_symm_C_X k σ i
  exact AlgHom.congr_fun h p

theorem optionPolynomialEquiv_X_some (e : VariableRing k τ ≃ₐ[k] VariableRing k σ) (i : τ) :
    optionPolynomialEquiv k τ σ e (MvPolynomial.X (some i))=MvPolynomial.rename some (e (MvPolynomial.X i)) := by
  simp [optionPolynomialEquiv,Polynomial.coe_mapAlgEquiv,optionEquivLeft_symm_C]
end NSP14.Homological
