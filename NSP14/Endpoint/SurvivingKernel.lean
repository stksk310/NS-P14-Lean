module
public import NSP14.Endpoint.CoreArtinBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : Data) (k : Type) [Field k]

theorem coreToG_zero_live_coeff (f : D.Core k) : D.coreToG k f=0 ↔
    ∀ p,D.coreDegree p=D.source.order (D.coreValue p).val → f.coeff p=0 := by
  change f∈(D.coreToG k).toLinearMap.ker ↔ _
  rw [D.coreToG_kernel_span]
  change f∈Submodule.span k ((fun p => AddMonoidAlgebra.single p (1:k)) ''
    {p | D.coreDegree p<D.source.order (D.coreValue p).val}) ↔ _
  rw [←AddMonoidAlgebra.supported_eq_span_single,AddMonoidAlgebra.mem_supported']
  constructor
  · intro h p hp
    exact h p (by change ¬D.coreDegree p<D.source.order (D.coreValue p).val;omega)
  · intro h p hp
    apply h p
    have := D.coreDegree_le_order p
    change ¬D.coreDegree p<D.source.order (D.coreValue p).val at hp
    omega

theorem core_endpointIdeal_map :
    Ideal.map (D.coreToG k) (NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k))=
      NSP14.Endpoint.endpointIdeal k (D.source.TangentAlgebra k) (D.endpointToG k) := by
  apply le_antisymm
  · exact Ideal.map_le_iff_le_comap.mpr (D.core_endpointIdeal_le k)
  · apply Ideal.span_le.mpr
    intro a ha
    have he (i : Fin 2) : D.coreToG k (D.endpointToCore k (MvPolynomial.X i))=D.endpointToG k (MvPolynomial.X i) :=
      AlgHom.congr_fun (D.coreToG_endpointToCore k) (MvPolynomial.X i)
    rcases (show a=D.endpointToG k (MvPolynomial.X 1) ∨ a=D.endpointToG k (MvPolynomial.X 0) by simpa using ha) with rfl|rfl
    · rw [←he 1]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))
    · rw [←he 0]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span (by simp))

/-- Exact coefficient kernel after killing endpoints in the actual G.
The surviving labels are precisely the live minimal core points. -/
theorem actualEndpointQuotient_coeff_zero (f : D.Core k) :
    Ideal.Quotient.mk (NSP14.Endpoint.endpointIdeal k (D.source.TangentAlgebra k) (D.endpointToG k)) (D.coreToG k f)=0 ↔
      ∀ p,D.CoreMinimal p → D.coreDegree p=D.source.order (D.coreValue p).val → f.coeff p=0 := by
  rw [Ideal.Quotient.eq_zero_iff_mem,←D.core_endpointIdeal_map k]
  change f∈Ideal.comap (D.coreToG k)
    (Ideal.map (D.coreToG k) (NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k))) ↔ _
  rw [Ideal.comap_map_of_surjective _ (D.coreToG_surjective k)]
  constructor
  · intro hf p hp hl
    obtain ⟨g,hg,h,hh,rfl⟩ := Submodule.mem_sup.mp hf
    have hg0 := (D.coreEndpointIdeal_coeff_zero k g).mp hg p hp
    have hh0 := (D.coreToG_zero_live_coeff k h).mp hh p hl
    simp only [AddMonoidAlgebra.coeff_add,Finsupp.add_apply,hg0,hh0,zero_add]
  · intro hf
    let g : D.Core k := AddMonoidAlgebra.ofCoeff (f.coeff.filter (fun p => ¬D.CoreMinimal p))
    have hg : g∈NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k) := by
      rw [D.coreEndpointIdeal_coeff_zero]
      intro p hp
      change (f.coeff.filter (fun p => ¬D.CoreMinimal p)) p=0
      exact Finsupp.filter_apply_neg _ _ (not_not.mpr hp)
    have hh : f-g∈Ideal.comap (D.coreToG k) ⊥ := by
      change D.coreToG k (f-g)=0
      rw [D.coreToG_zero_live_coeff]
      intro p hl
      change f.coeff p-(f.coeff.filter (fun p => ¬D.CoreMinimal p)) p=0
      by_cases hp : D.CoreMinimal p
      · simp only [Finsupp.filter_apply,ite_eq_right (not_not.mpr hp),hf p hp hl,sub_self]
      · simp only [Finsupp.filter_apply,ite_eq_left hp,sub_self]
    exact Submodule.mem_sup.mpr ⟨g,hg,f-g,hh,by abel⟩
end NSP14.Endpoint.Data
