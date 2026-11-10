module
public import NSP14.Ordinary.CutFirstOrder
public import NSP14.Ordinary.TowerEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable def headToStageTwo : S.HeadAlgebra k →ₐ[S.PolynomialRing k] S.TowerStage k 2 :=
  Ideal.Quotient.mkₐ (S.PolynomialRing k) (S.jumpIdeal k (2-1))

theorem headToStageTwo_injective : Function.Injective (S.headToStageTwo k) := by
  intro a b hab
  have hz : S.headToStageTwo k (a-b)=0 := by rw [map_sub,hab,sub_self]
  have hm : a-b ∈ S.jumpIdeal k 1 := Ideal.Quotient.eq_zero_iff_mem.mp hz
  rw [S.jumpIdeal_one] at hm
  exact sub_eq_zero.mp hm

theorem headToStageTwo_surjective : Function.Surjective (S.headToStageTwo k) := Ideal.Quotient.mk_surjective

noncomputable def headStageTwoEquiv : S.HeadAlgebra k ≃ₐ[S.PolynomialRing k] S.TowerStage k 2 :=
  AlgEquiv.ofBijective (S.headToStageTwo k) ⟨S.headToStageTwo_injective k,S.headToStageTwo_surjective k⟩

noncomputable def highToStageTwo : (S.highIdeal k 2) →ₗ[S.PolynomialRing k] (S.towerHighIdeal k 2 2) where
  toFun a := ⟨S.headToStageTwo k a.val,Ideal.mem_map_of_mem _ a.property⟩
  map_add' _a _b := Subtype.ext (map_add _ _ _)
  map_smul' p a := Subtype.ext ((S.headToStageTwo k).toLinearMap.map_smul p a.val)

theorem highToStageTwo_bijective : Function.Bijective (S.highToStageTwo k) := by
  constructor
  · intro a b hab
    exact Subtype.ext (S.headToStageTwo_injective k (congrArg Subtype.val hab))
  · intro a
    obtain ⟨b,hb,he⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp a.property
    exact ⟨⟨b,hb⟩,Subtype.ext he⟩

noncomputable def highStageTwoEquiv : (S.highIdeal k 2) ≃ₗ[S.PolynomialRing k] (S.towerHighIdeal k 2 2) :=
  LinearEquiv.ofBijective (S.highToStageTwo k) (S.highToStageTwo_bijective k)

namespace LinearCutData
variable {S k} (C : S.LinearCutData k)

/-- The actual stage-two high part uses the same cut: its denominator is
F_1=0, so it is the actual degree>=2 part of A. -/
noncomputable def cutHeadHighTwoIso : C.cutHeadHigh ≅ C.cutHigh 2 2 :=
  C.restrictFunctor.mapIso (S.highStageTwoEquiv k).toModuleIso

theorem cutHeadHighEuler_two (j : ℕ) : C.cutHeadHighEuler j=C.cutHighEuler 2 2 j := by
  let := C.cutHeadHigh_finite
  let := C.cutHigh_finite 2 2
  exact congrArg (fun b : ℕ → ℕ => partialEuler b j)
    (funext (totalBetti_iso k (Fin S.actualCutRank) C.cutHeadHighTwoIso))
end LinearCutData
end NSP14.NumericalSemigroup
