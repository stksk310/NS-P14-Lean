module
public import NSP14.Endpoint.MonomialQuotient
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint
variable (k : Type) [Field k] (U : Set (ℕ×ℕ))
  (hU : ∀ {a b},a∈U → a≤b → b∈U)

noncomputable def coordinateQuotientCoefficient (c : {c : ℕ×ℕ // c∉U}) :
    (MvPolynomial (Fin 2) k ⧸ coordinateIdeal k U) →ₗ[k] k :=
  ((coordinateIdeal k U).restrictScalars k).liftQ
    ((Finsupp.lapply (exponentPairEquiv c.val)).comp (AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap) (by
      intro f hf
      change f.coeff (exponentPairEquiv c.val)=0
      by_contra hne
      have hmem := (coordinateIdeal_mem k U hU f).mp hf _ (Finsupp.mem_support_iff.mpr hne)
      change exponentPairEquiv.symm (exponentPairEquiv c.val)∈U at hmem
      rw [AddEquiv.symm_apply_apply] at hmem
      exact c.property hmem)

theorem coordinateQuotientCoefficient_mk (c : {c : ℕ×ℕ // c∉U}) (f : MvPolynomial (Fin 2) k) :
    coordinateQuotientCoefficient k U hU c (Ideal.Quotient.mk _ f)=f.coeff (exponentPairEquiv c.val) := rfl

theorem coordinateQuotientBasis_coord (c : {c : ℕ×ℕ // c∉U}) :
    (coordinateQuotientBasis k U hU).coord c=coordinateQuotientCoefficient k U hU c := by
  apply (coordinateQuotientBasis k U hU).ext
  intro b
  change ((coordinateQuotientBasis k U hU).repr (coordinateQuotientBasis k U hU b)) c=_
  rw [Module.Basis.repr_self,coordinateQuotientBasis_apply,coordinateQuotientCoefficient_mk,
    MvPolynomial.coeff_monomial]
  have he : exponentPairEquiv b.val=exponentPairEquiv c.val ↔ b=c :=
    ⟨fun h => Subtype.ext (exponentPairEquiv.injective h),fun h => by rw [h]⟩
  simp only [Finsupp.single_apply,he]

theorem coordinateQuotientBasis_repr_mk (c : {c : ℕ×ℕ // c∉U}) (f : MvPolynomial (Fin 2) k) :
    (coordinateQuotientBasis k U hU).repr (Ideal.Quotient.mk _ f) c=f.coeff (exponentPairEquiv c.val) := by
  change (coordinateQuotientBasis k U hU).coord c (Ideal.Quotient.mk _ f)=_
  rw [coordinateQuotientBasis_coord,coordinateQuotientCoefficient_mk]
end NSP14.Endpoint
