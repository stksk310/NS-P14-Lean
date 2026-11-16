module
public import NSP14.Endpoint.InternalMonoid
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : Data) (k : Type) [Field k]

theorem internalToCore_monomial (β : D.a →₀ ℕ) (c : k) :
    D.internalToCore k (MvPolynomial.monomial β c)=AddMonoidAlgebra.single (D.internalPoint β) c := by
  rw [D.internalToCore_mapDomain]
  exact AddMonoidAlgebra.mapDomain_single

theorem QCore_internal_monomial_zero (β : D.a →₀ ℕ) :
    D.internalToQCore k (MvPolynomial.monomial β 1)=0 ↔ ¬D.CoreMinimal (D.internalPoint β) := by
  change Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.monomial β 1))=0 ↔ _
  rw [D.internalToCore_monomial,Ideal.Quotient.eq_zero_iff_mem,D.coreEndpointIdeal_mem]
  constructor
  · intro h
    exact h _ (by simp [AddMonoidAlgebra.coeff_single])
  · intro h p hp
    have he : p=D.internalPoint β := by
      simpa [AddMonoidAlgebra.coeff_single] using hp
    exact he ▸ h

/-- Two internal offsets give independent pure-word coordinates.
Consequently no cancellation between distinct internal monomials can
create an additional relation in QC. This statement is only for q=2. -/
theorem two_internal_monomial_kernel (hq : D.q=2) (f : D.InternalRing k) :
    D.internalToQCore k f=0 ↔ ∀ β∈f.support,D.internalToQCore k (MvPolynomial.monomial β (1:k))=0 := by
  constructor
  · intro hf β hβ
    apply (D.QCore_internal_monomial_zero k β).mpr
    intro hmin
    change Ideal.Quotient.mk _ (D.internalToCore k f)=0 at hf
    have hc := (D.coreEndpointIdeal_coeff_zero k _).mp (Ideal.Quotient.eq_zero_iff_mem.mp hf)
      (D.internalPoint β) hmin
    rw [D.internalToCore_mapDomain] at hc
    change (AddMonoidAlgebra.mapDomain D.internalPoint f).coeff (D.internalPoint β)=0 at hc
    rw [AddMonoidAlgebra.coeff_mapDomain,Finsupp.mapDomain_apply_of_injective (D.internalPoint_injective_two hq)] at hc
    exact (Finsupp.mem_support_iff.mp hβ) hc
  · intro h
    have hm : f∈Ideal.span ((fun β : D.a →₀ ℕ => MvPolynomial.monomial β (1:k)) ''
        {β | D.internalToQCore k (MvPolynomial.monomial β (1:k))=0}) := by
      apply MvPolynomial.mem_ideal_span_monomial_image.mpr
      intro β hβ
      exact ⟨β,h β hβ,le_rfl⟩
    have hi : Ideal.span ((fun β : D.a →₀ ℕ => MvPolynomial.monomial β (1:k)) ''
        {β | D.internalToQCore k (MvPolynomial.monomial β (1:k))=0})≤
          RingHom.ker (D.internalToQCore k).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨β,hβ,rfl⟩
      exact hβ
    exact hi hm

/-- The actual defining kernel is a monomial ideal, not merely an
initial ideal or a dimension model. -/
theorem two_internal_kernel_ideal (hq : D.q=2) :
    RingHom.ker (D.internalToQCore k).toRingHom=
      Ideal.span ((fun β : D.a →₀ ℕ => MvPolynomial.monomial β (1:k)) ''
        {β | ¬D.CoreMinimal (D.internalPoint β)}) := by
  apply le_antisymm
  · intro f hf
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro β hβ
    exact ⟨β,(D.QCore_internal_monomial_zero k β).mp ((D.two_internal_monomial_kernel k hq f).mp hf β hβ),le_rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨β,hβ,rfl⟩
    exact (D.QCore_internal_monomial_zero k β).mpr hβ
end NSP14.Endpoint.Data
