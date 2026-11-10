module
public import NSP14.Homological.LinearVariables
public import NSP14
@[expose] public section
open NSP14.Homological
namespace LinearVariablesAcceptance
variable {k V : Type} [Field k] [AddCommGroup V] [Module k V]
theorem preserve_cut_prefix {n t : ℕ} (c : Fin n → V) (hc : LinearIndependent k c)
    (hd : n+t ≤ Module.finrank k V) :
    ∃ d : Fin (n+t) → V, LinearIndependent k d ∧ ∀ i, d (Fin.castAdd t i)=c i :=
  extend_independent_prefix c hc hd

theorem polynomial_inverse {σ τ : Type} [Fintype σ] [Fintype τ]
    (e : (τ → k) ≃ₗ[k] (σ → k)) (p : MvPolynomial τ k) :
    (polynomialLinearEquiv e).symm (polynomialLinearEquiv e p)=p :=
  (polynomialLinearEquiv e).symm_apply_apply p
end LinearVariablesAcceptance
