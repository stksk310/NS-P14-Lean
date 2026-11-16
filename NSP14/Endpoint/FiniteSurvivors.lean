module
public import NSP14.Endpoint.FiniteOrder
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : Data)

noncomputable def survivingComputedEquiv : D.SurvivingMinimalIndex ≃
    (Σ r : Fin D.u,{c : ℕ×ℕ // c∈D.computedSurvivors r}) where
  toFun p := ⟨(D.coreCoordinates p.val).1,⟨(D.coreCoordinates p.val).2,
    (D.computedSurvivors_iff _ _).mpr ⟨p.property.1,by
      rw [D.decode_coreCoordinates]
      exact p.property.2⟩⟩⟩
  invFun c := ⟨⟨D.decodeCoordinate (c.1,c.2.val),((D.computedSurvivors_iff _ _).mp c.2.property).1.prop⟩,
    by
      constructor
      · change Minimal (·∈D.coreFiber (D.coreCoordinates _).1) (D.coreCoordinates _).2
        rw [D.coreCoordinates_decode]
        exact ((D.computedSurvivors_iff _ _).mp c.2.property).1
      · exact ((D.computedSurvivors_iff _ _).mp c.2.property).2⟩
  left_inv p := by
    apply Subtype.ext
    exact Subtype.ext (D.decode_coreCoordinates p.val)
  right_inv c := by
    rcases c with ⟨r,c,hc⟩
    have he := D.coreCoordinates_decode r c ((D.computedSurvivors_iff _ _).mp hc).1.prop
    exact Sigma.subtype_ext (congrArg Prod.fst he) (congrArg Prod.snd he)

variable (k : Type) [Field k]
theorem actualP_computed : D.actualP k=∑ r : Fin D.u,(D.computedSurvivors r).card := by
  rw [D.actualP_survivingCount,Nat.card_congr D.survivingComputedEquiv,Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_coe _
end NSP14.Endpoint.Data
