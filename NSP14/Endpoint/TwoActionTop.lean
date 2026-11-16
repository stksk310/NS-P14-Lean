module
public import NSP14.Endpoint.SingleAction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.Endpoint
variable (R : Type) [CommRing R] (r s : R) (M : ModuleCat.{0} R)

noncomputable def twoActionTopEquiv : (actionKoszul R [s,r] M).X 2 ≃ₗ[R] M where
  toFun z := singleActionOneEquiv R r M (coneFirst (actionKoszul R [r] M) s 1 z)
  invFun a := homotopyCofiber.inlX (s • 𝟙 (actionKoszul R [r] M)) 1 2 rfl ((singleActionOneEquiv R r M).symm a)
  map_add' a b := by rw [map_add,map_add]
  map_smul' c a := by rw [map_smul,map_smul];rfl
  left_inv z := by
    apply cone_element_ext (actionKoszul R [r] M) s 1
    · erw [coneFirst_inl,LinearEquiv.symm_apply_apply]
    · have : Subsingleton ((actionKoszul R [r] M).X 2) :=
        ModuleCat.subsingleton_of_isZero (action_piece_isZero_of_gt R [r] M 2 (by simp))
      exact Subsingleton.elim _ _
  right_inv a := by
    dsimp only
    erw [coneFirst_inl]
    exact LinearEquiv.apply_symm_apply _ _

theorem twoAction_top_cycle (z : (actionKoszul R [s,r] M).X 2) :
    (actionKoszul R [s,r] M).d 2 1 z=0 ↔
      r • twoActionTopEquiv R r s M z=0 ∧ s • twoActionTopEquiv R r s M z=0 := by
  let K := actionKoszul R [r] M
  have hz2 : coneSecond K s 2 z=0 := by
    have : Subsingleton (K.X 2) := ModuleCat.subsingleton_of_isZero
      (action_piece_isZero_of_gt R [r] M 2 (by simp))
    exact Subsingleton.elim _ _
  have hfirst := cone_d_first K s 0 z
  have hsecond := cone_d_second K s 1 z
  rw [hz2,map_zero,add_zero] at hsecond
  change coneFirst K s 0 ((actionKoszul R [s,r] M).d 2 1 z)= -K.d 1 0 (coneFirst K s 1 z) at hfirst
  change coneSecond K s 1 ((actionKoszul R [s,r] M).d 2 1 z)=s • coneFirst K s 1 z at hsecond
  constructor
  · intro hcycle
    rw [hcycle,map_zero] at hfirst hsecond
    have hd : K.d 1 0 (coneFirst K s 1 z)=0 := neg_eq_zero.mp hfirst.symm
    constructor
    · change r • singleActionOneEquiv R r M (coneFirst K s 1 z)=0
      rw [←singleAction_differential]
      change (actionZeroIso R [r] M).hom (K.d 1 0 (coneFirst K s 1 z))=0
      rw [hd,map_zero]
    · have h := congrArg (singleActionOneEquiv R r M) hsecond.symm
      rw [map_smul,map_zero] at h
      exact h
  · rintro ⟨hr,hs⟩
    apply cone_element_ext K s 0
    · rw [map_zero,hfirst]
      have hd : K.d 1 0 (coneFirst K s 1 z)=0 := by
        apply (actionZeroIso R [r] M).toLinearEquiv.injective
        change actionZeroDifferential R [r] M (coneFirst K s 1 z)=(actionZeroIso R [r] M).hom 0
        rw [singleAction_differential,map_zero]
        exact hr
      rw [hd,neg_zero]
    · rw [map_zero,hsecond]
      apply (singleActionOneEquiv R r M).injective
      rw [map_smul,map_zero]
      exact hs

noncomputable def twoActionCycleEquiv : ((actionKoszul R [s,r] M).d 2 1).hom.ker ≃ₗ[R]
    ↥((r • 𝟙 M).hom.ker⊓(s • 𝟙 M).hom.ker) where
  toFun z := ⟨twoActionTopEquiv R r s M z.val,(twoAction_top_cycle R r s M z.val).mp z.property⟩
  invFun z := ⟨(twoActionTopEquiv R r s M).symm z.val,by
    apply (twoAction_top_cycle R r s M _).mpr
    rw [LinearEquiv.apply_symm_apply]
    exact z.property⟩
  left_inv z := Subtype.ext ((twoActionTopEquiv R r s M).symm_apply_apply z.val)
  right_inv z := Subtype.ext ((twoActionTopEquiv R r s M).apply_symm_apply z.val)
  map_add' a b := Subtype.ext ((twoActionTopEquiv R r s M).map_add a.val b.val)
  map_smul' c a := Subtype.ext ((twoActionTopEquiv R r s M).map_smul c a.val)

noncomputable def twoActionH2Equiv : (actionKoszul R [s,r] M).homology 2 ≃ₗ[R]
    ↥((r • 𝟙 M).hom.ker⊓(s • 𝟙 M).hom.ker) := by
  let K := actionKoszul R [s,r] M
  have hf : (K.sc' 3 2 1).f=0 :=
    (action_piece_isZero_of_gt R [s,r] M 3 (by simp)).eq_of_src _ _
  exact ((K.homologyIsoSc' 3 2 1 ((ComplexShape.down ℕ).prev_eq' rfl) ((ComplexShape.down ℕ).next_eq' rfl)) ≪≫
    ((K.sc' 3 2 1).asIsoHomologyπ hf).symm ≪≫
    (K.sc' 3 2 1).moduleCatCyclesIso).toLinearEquiv.trans (twoActionCycleEquiv R r s M)
end NSP14.Endpoint
