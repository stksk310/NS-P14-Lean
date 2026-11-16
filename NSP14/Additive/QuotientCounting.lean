module
public import NSP14.Additive.Kneser
@[expose] public section
open scoped Pointwise Classical
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
noncomputable def quotientImage (A : Finset G) (H : AddSubgroup G) : Finset (G ⧸ H) :=
  A.image QuotientAddGroup.mk

theorem coe_thicken (A : Finset G) (H : AddSubgroup G) :
    (thicken A H : Set G) = (A : Set G) + (H : Set G) := by
  simp [thicken]

theorem thicken_preimage (A : Finset G) (H : AddSubgroup G) :
    (thicken A H : Set G) =
      QuotientAddGroup.mk ⁻¹' (quotientImage A H : Set (G ⧸ H)) := by
  rw [coe_thicken, quotientImage, Finset.coe_image,
    QuotientAddGroup.preimage_image_mk_eq_add]

/-- Exact coset count, valid for every subgroup, including top and bottom. -/
theorem card_thicken (A : Finset G) (H : AddSubgroup G) :
    (thicken A H).card = Nat.card H * (quotientImage A H).card := by
  have e := QuotientAddGroup.preimageMkEquivAddSubgroupProdSet H
    (quotientImage A H : Set (G ⧸ H))
  rw [←thicken_preimage] at e
  have hc := Nat.card_congr e
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod,
    Finset.coe_sort_coe, Fintype.card_coe] using hc

omit [Fintype G] [DecidableEq G] in
theorem quotientImage_stabilizer (S : Finset G) :
    sumStabilizer (quotientImage S (sumStabilizer S)) = ⊥ := by
  unfold sumStabilizer quotientImage
  simpa only [Finset.coe_image] using AddAction.stabilizer_image_coe_quotient (S : Set G)

theorem card_saturated (S : Finset G) (H : AddSubgroup G) (hS : thicken S H = S) :
    S.card = Nat.card H*(quotientImage S H).card := by
  nth_rw 1 [←hS]
  exact card_thicken S H

/-- Exact stabilizer identification for every quotient, before specializing
H to the actual stabilizer. -/
theorem quotient_stabilizer_preimage (A : Finset G) (H : AddSubgroup G) (g : G) :
    (QuotientAddGroup.mk g : G ⧸ H) ∈ sumStabilizer (quotientImage A H) ↔
      g ∈ sumStabilizer (thicken A H) := by
  unfold sumStabilizer
  rw [AddAction.mem_stabilizer_set,AddAction.mem_stabilizer_set,thicken_preimage A H]
  simp only [Set.mem_preimage,vadd_eq_add]
  constructor
  · intro hh x
    have he : (QuotientAddGroup.mk (g+x) : G ⧸ H) =
        QuotientAddGroup.mk g+QuotientAddGroup.mk x := (QuotientAddGroup.mk' H).map_add g x
    rw [he]
    exact hh (QuotientAddGroup.mk x)
  · intro hh q
    obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective q
    have he : (QuotientAddGroup.mk (g+x) : G ⧸ H) =
        QuotientAddGroup.mk g+QuotientAddGroup.mk x := (QuotientAddGroup.mk' H).map_add g x
    rw [←he]
    exact hh x
end NSP14.Additive
