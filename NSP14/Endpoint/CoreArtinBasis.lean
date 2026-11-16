module
public import NSP14.Endpoint.CoreArtinIdeal
public import NSP14.Endpoint.Volume
public import NSP14.Endpoint.ArtinTransport
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

abbrev CoreMinimalIndex := {p : D.corePoints // D.CoreMinimal p}

noncomputable def coreMinimalIndexEquiv : D.CoreMinimalIndex ≃
    (Σ r : Fin D.u,{c : ℕ×ℕ // Minimal (·∈D.coreFiber r) c}) where
  toFun p := ⟨(D.coreCoordinates p.val).1,⟨(D.coreCoordinates p.val).2,p.property⟩⟩
  invFun c := ⟨⟨D.decodeCoordinate (c.1,c.2.val),c.2.property.prop⟩,by
    change Minimal (·∈D.coreFiber (D.coreCoordinates _).1) (D.coreCoordinates _).2
    rw [D.coreCoordinates_decode]
    exact c.2.property⟩
  left_inv p := by
    apply Subtype.ext
    exact Subtype.ext (D.decode_coreCoordinates p.val)
  right_inv c := by
    rcases c with ⟨r,c,hc⟩
    change (⟨(D.coreCoordinates ⟨D.decodeCoordinate (r,c),hc.prop⟩).1,
      ⟨(D.coreCoordinates ⟨D.decodeCoordinate (r,c),hc.prop⟩).2,_⟩⟩ : Σ r,{c // Minimal (·∈D.coreFiber r) c})=⟨r,⟨c,hc⟩⟩
    have he := D.coreCoordinates_decode r c hc.prop
    exact Sigma.subtype_ext (congrArg Prod.fst he) (congrArg Prod.snd he)

noncomputable instance coreMinimalIndexFinite : Finite D.CoreMinimalIndex := by
  have (r : Fin D.u) : Finite {c | Minimal (·∈D.coreFiber r) c} := (D.minimalFiber_finite r).to_subtype
  exact Finite.of_equiv _ D.coreMinimalIndexEquiv.symm

noncomputable instance coreMinimalIndexFintype : Fintype D.CoreMinimalIndex := Fintype.ofFinite _

variable (k : Type) [Field k]
noncomputable def coreMinimalNormal : (D.CoreMinimalIndex →₀ k) →ₗ[k] D.Core k :=
  (AddMonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.comp
    ((Finsupp.supported k k {p : D.corePoints | D.CoreMinimal p}).subtype.comp
      (Finsupp.supportedEquivFinsupp (R:=k) {p : D.corePoints | D.CoreMinimal p}).symm.toLinearMap)

theorem coreMinimalNormal_coeff (g : D.CoreMinimalIndex →₀ k) :
    (D.coreMinimalNormal k g).coeff=g.extendDomain := rfl

noncomputable def QCoreNormalMap : (D.CoreMinimalIndex →₀ k) →ₗ[k] D.QCore k :=
  (Ideal.Quotient.mkₐ k _).toLinearMap.comp (D.coreMinimalNormal k)

theorem QCoreNormalMap_injective : Function.Injective (D.QCoreNormalMap k) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro g hg
  change Ideal.Quotient.mk _ (D.coreMinimalNormal k g)=0 at hg
  have hm := (D.coreEndpointIdeal_coeff_zero k _).mp (Ideal.Quotient.eq_zero_iff_mem.mp hg)
  apply Finsupp.ext
  intro p
  have hh := hm p.val p.property
  rw [D.coreMinimalNormal_coeff] at hh
  simpa only [Finsupp.extendDomain_apply,dite_eq_left p.property,Finsupp.zero_apply] using hh

theorem QCoreNormalMap_surjective : Function.Surjective (D.QCoreNormalMap k) := by
  intro a
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ a
  let g : D.CoreMinimalIndex →₀ k := f.coeff.subtypeDomain D.CoreMinimal
  refine ⟨g,?_⟩
  change Ideal.Quotient.mk _ (D.coreMinimalNormal k g)=Ideal.Quotient.mk _ f
  apply Ideal.Quotient.eq.mpr
  apply (D.coreEndpointIdeal_coeff_zero k _).mpr
  intro p hp
  simp only [AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,D.coreMinimalNormal_coeff,
    Finsupp.extendDomain_apply,dite_eq_left hp,g,Finsupp.subtypeDomain_apply,sub_self]

/-- Coordinates in the genuine ring quotient QC, indexed by actual
minimal fiber points. No initial ideal or monomial assumption on T is used. -/
noncomputable def QCoreCoordinates : D.QCore k ≃ₗ[k] (D.CoreMinimalIndex →₀ k) :=
  (LinearEquiv.ofBijective (D.QCoreNormalMap k) ⟨D.QCoreNormalMap_injective k,D.QCoreNormalMap_surjective k⟩).symm

noncomputable def QCoreBasis : Module.Basis D.CoreMinimalIndex k (D.QCore k) :=
  Finsupp.basisSingleOne.map (D.QCoreCoordinates k).symm

theorem QCoreBasis_apply (p : D.CoreMinimalIndex) : D.QCoreBasis k p=
    Ideal.Quotient.mk _ (D.coreMonomial k p.val) := by
  change Ideal.Quotient.mk _ (D.coreMinimalNormal k (Finsupp.single p (1:k)))=_
  apply congrArg (Ideal.Quotient.mk _)
  apply (AddMonoidAlgebra.coeffLinearEquiv k).injective
  change (D.coreMinimalNormal k (Finsupp.single p (1:k))).coeff=(D.coreMonomial k p.val).coeff
  rw [D.coreMinimalNormal_coeff,Finsupp.extendDomain_single]
  rfl

theorem coreP_minimalCount : D.coreP k=∑ r : Fin D.u,(D.minimalPoints r).card := by
  rw [coreP,Module.finrank_eq_card_basis (D.QCoreBasis k)]
  have (r : Fin D.u) : Finite {c | Minimal (·∈D.coreFiber r) c} := (D.minimalFiber_finite r).to_subtype
  rw [Fintype.card_eq_nat_card,Nat.card_congr D.coreMinimalIndexEquiv,Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  exact (D.minimalPoints_card_eq r).symm

theorem coreP_le_wordVolume : D.coreP k≤D.wordVolume := by
  rw [D.coreP_minimalCount]
  exact D.minimalCount_volume
end NSP14.Endpoint.Data
