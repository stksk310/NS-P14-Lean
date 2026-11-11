module
public import NSP14.Endpoint.FiberIndices
public import NSP14.Homological.StandardMonomials
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
namespace NSP14.Endpoint
variable (k : Type) [Field k] (U : Set (ℕ×ℕ))
  (hU : ∀ {a b},a∈U → a≤b → b∈U)

include hU in
theorem coordinateStandard_iff (β : Fin 2 →₀ ℕ) :
    β∈StandardExponent MonomialOrder.degLex (coordinateIdeal k U) ↔ (β 0,β 1)∉U := by
  constructor
  · intro h hβ
    have hm : MvPolynomial.monomial β (1:k)∈coordinateIdeal k U := Ideal.subset_span ⟨β,hβ,rfl⟩
    have hne : MvPolynomial.monomial β (1:k)≠0 := by simp
    have hdeg : MonomialOrder.degLex.degree (MvPolynomial.monomial β (1:k))=β := by
      rw [MonomialOrder.degree_monomial]
      simp
    exact h _ hm hne (by rw [hdeg])
  · intro hβ f hf hf0 hle
    have hd := (coordinateIdeal_mem k U hU f).mp hf _ (MonomialOrder.degLex.degree_mem_support hf0)
    exact hβ (hU hd ⟨hle 0,hle 1⟩)

noncomputable def coordinateStandardEquiv :
    StandardExponent MonomialOrder.degLex (coordinateIdeal k U) ≃ {c : ℕ×ℕ // c∉U} where
  toFun β := ⟨(β.val 0,β.val 1),(coordinateStandard_iff k U hU β.val).mp β.property⟩
  invFun c := ⟨exponentPairEquiv c.val,(coordinateStandard_iff k U hU _).mpr (by
    change exponentPairEquiv.symm (exponentPairEquiv c.val)∉U
    rw [AddEquiv.symm_apply_apply]
    exact c.property)⟩
  left_inv β := Subtype.ext (exponentPairEquiv.apply_symm_apply β.val)
  right_inv c := Subtype.ext (exponentPairEquiv.symm_apply_apply c.val)

noncomputable def coordinateQuotientBasis : Module.Basis {c : ℕ×ℕ // c∉U} k
    (MvPolynomial (Fin 2) k ⧸ coordinateIdeal k U) :=
  (standardMonomialBasis MonomialOrder.degLex (coordinateIdeal k U)).reindex (coordinateStandardEquiv k U hU)

theorem coordinateQuotientBasis_apply (c : {c : ℕ×ℕ // c∉U}) :
    coordinateQuotientBasis k U hU c=Ideal.Quotient.mk _ (MvPolynomial.monomial (exponentPairEquiv c.val) (1:k)) := by
  rw [coordinateQuotientBasis,Module.Basis.reindex_apply,standardMonomialBasis_apply]
  rfl
end NSP14.Endpoint
