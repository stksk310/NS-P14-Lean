module
public import NSP14.Endpoint.SurvivingKernel
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : Data)

abbrev SurvivingMinimalIndex := {p : D.corePoints // D.CoreMinimal p ∧
  D.coreDegree p=D.source.order (D.coreValue p).val}

instance survivingMinimalFinite : Finite D.SurvivingMinimalIndex :=
  Finite.of_injective (fun p : D.SurvivingMinimalIndex => (⟨p.val,p.property.1⟩ : D.CoreMinimalIndex))
    (by intro a b h;exact Subtype.ext (congrArg (fun p : D.CoreMinimalIndex => p.val) h))
noncomputable instance survivingMinimalFintype : Fintype D.SurvivingMinimalIndex := Fintype.ofFinite _

variable (k : Type) [Field k]
noncomputable def survivingNormal : (D.SurvivingMinimalIndex →₀ k) →ₗ[k] D.Core k :=
  (AddMonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.comp
    ((Finsupp.supported k k {p : D.corePoints | D.CoreMinimal p ∧
      D.coreDegree p=D.source.order (D.coreValue p).val}).subtype.comp
        (Finsupp.supportedEquivFinsupp (R:=k) {p : D.corePoints | D.CoreMinimal p ∧
          D.coreDegree p=D.source.order (D.coreValue p).val}).symm.toLinearMap)
theorem survivingNormal_coeff (g : D.SurvivingMinimalIndex →₀ k) :
    (D.survivingNormal k g).coeff=g.extendDomain := by
  change ((Finsupp.supportedEquivFinsupp (R:=k) {p : D.corePoints | D.CoreMinimal p ∧
    D.coreDegree p=D.source.order (D.coreValue p).val}).symm g).val=g.extendDomain
  exact Finsupp.supportedEquivFinsupp_symm_apply_coe
    {p : D.corePoints | D.CoreMinimal p ∧ D.coreDegree p=D.source.order (D.coreValue p).val} g

noncomputable def QActualNormalMap : (D.SurvivingMinimalIndex →₀ k) →ₗ[k] D.QActual k :=
  (Ideal.Quotient.mkₐ k _).toLinearMap.comp ((D.coreToG k).toLinearMap.comp (D.survivingNormal k))

theorem QActualNormalMap_injective : Function.Injective (D.QActualNormalMap k) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro g hg
  have hm := (D.actualEndpointQuotient_coeff_zero k _).mp hg
  ext p
  have h := hm p.val p.property.1 p.property.2
  rw [D.survivingNormal_coeff] at h
  simpa only [Finsupp.extendDomain_apply,dite_eq_left p.property,Finsupp.zero_apply] using h

theorem QActualNormalMap_surjective : Function.Surjective (D.QActualNormalMap k) := by
  intro a
  obtain ⟨v,rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ a
  obtain ⟨f,rfl⟩ := D.coreToG_surjective k v
  let g : D.SurvivingMinimalIndex →₀ k := f.coeff.subtypeDomain _
  refine ⟨g,?_⟩
  change Ideal.Quotient.mk _ (D.coreToG k (D.survivingNormal k g))=Ideal.Quotient.mk _ (D.coreToG k f)
  apply Ideal.Quotient.eq.mpr
  rw [←map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply (D.actualEndpointQuotient_coeff_zero k _).mpr
  intro p hp hl
  rw [AddMonoidAlgebra.coeff_sub,D.survivingNormal_coeff]
  change g.extendDomain p-f.coeff p=0
  simp only [Finsupp.extendDomain_apply,dite_eq_left (show D.CoreMinimal p ∧
      D.coreDegree p=D.source.order (D.coreValue p).val from ⟨hp,hl⟩),g,Finsupp.subtypeDomain_apply,sub_self]

noncomputable def QActualCoordinates : D.QActual k ≃ₗ[k] (D.SurvivingMinimalIndex →₀ k) :=
  (LinearEquiv.ofBijective (D.QActualNormalMap k)
    ⟨D.QActualNormalMap_injective k,D.QActualNormalMap_surjective k⟩).symm
noncomputable def QActualBasis : Module.Basis D.SurvivingMinimalIndex k (D.QActual k) :=
  Finsupp.basisSingleOne.map (D.QActualCoordinates k).symm

theorem QActualBasis_apply (p : D.SurvivingMinimalIndex) : D.QActualBasis k p=
    Ideal.Quotient.mk _ (D.coreToG k (D.coreMonomial k p.val)) := by
  change Ideal.Quotient.mk _ (D.coreToG k (D.survivingNormal k (Finsupp.single p 1)))=_
  apply congrArg (fun f => Ideal.Quotient.mk _ (D.coreToG k f))
  apply AddMonoidAlgebra.coeff_injective
  rw [D.survivingNormal_coeff]
  change (Finsupp.single p (1:k)).extendDomain=Finsupp.single p.val 1
  exact Finsupp.extendDomain_single _ _

theorem actualP_survivingCount : D.actualP k=Nat.card D.SurvivingMinimalIndex := by
  rw [actualP,Module.finrank_eq_card_basis (D.QActualBasis k),Nat.card_eq_fintype_card]
end NSP14.Endpoint.Data
