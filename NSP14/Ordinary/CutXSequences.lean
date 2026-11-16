module
public import NSP14.Ordinary.CutFinite
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

/-- Actual multiplication by x, retaining the same P action. -/
noncomputable def cutX : C.cutG ⟶ C.cutG := ModuleCat.ofHom (X:=C.cutG) (Y:=C.cutG)
  { toFun a := (show S.TangentAlgebra k from a)*S.xElement k
    map_add' a b := by
      change ((show S.TangentAlgebra k from a)+(show S.TangentAlgebra k from b))*S.xElement k=_
      exact add_mul _ _ _
    map_smul' p a := by
      change (S.polynomialToG k (C.toPolynomialRing p)*(show S.TangentAlgebra k from a))*S.xElement k=
        S.polynomialToG k (C.toPolynomialRing p)*((show S.TangentAlgebra k from a)*S.xElement k)
      exact mul_assoc _ _ _ }

theorem cutX_apply (a : C.cutG) : C.cutX a=S.xMultiply k (show S.TangentAlgebra k from a) := rfl

theorem cutX_mem_range (a : C.cutG) : a ∈ C.cutX.hom.range ↔
    (show S.TangentAlgebra k from a) ∈ (S.xMultiply k).range := by
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨(show S.TangentAlgebra k from b),hb⟩
  · rintro ⟨b,hb⟩
    exact ⟨(show C.cutG from b),hb⟩

noncomputable def cutXImage : ModuleCat (S.CutPolynomialRing k) :=
  ModuleCat.of (S.CutPolynomialRing k) C.cutX.hom.range

noncomputable def cutTerminalInclusion : C.cutT ⟶ C.cutG := ModuleCat.ofHom (X:=C.cutT) (Y:=C.cutG)
  { toFun a := a.val
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }

noncomputable def cutXRangeProjection : C.cutG ⟶ C.cutXImage :=
  ModuleCat.ofHom (X:=C.cutG) (Y:=C.cutXImage) C.cutX.hom.rangeRestrict

noncomputable def cutXRangeInclusion : C.cutXImage ⟶ C.cutG :=
  ModuleCat.ofHom (X:=C.cutXImage) (Y:=C.cutG) C.cutX.hom.range.subtype

noncomputable def cutHeadProjection : C.cutG ⟶ C.cutA := ModuleCat.ofHom (X:=C.cutG) (Y:=C.cutA)
  { toFun a := S.toHeadAlgebra k a
    map_add' a b := map_add _ a b
    map_smul' p a := by
      change S.toHeadAlgebra k (S.polynomialToG k (C.toPolynomialRing p)*(show S.TangentAlgebra k from a))=
        S.polynomialToA k (C.toPolynomialRing p)*S.toHeadAlgebra k a
      rw [map_mul]
      rfl }

theorem cutTerminalInclusion_comp : C.cutTerminalInclusion ≫ C.cutXRangeProjection=0 := by
  ext a
  apply Subtype.ext
  exact a.property

theorem cutXRangeInclusion_comp : C.cutXRangeInclusion ≫ C.cutHeadProjection=0 := by
  ext a
  change Ideal.Quotient.mk (S.xIdeal k) a.val=0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change a.val ∈ (S.xIdeal k).restrictScalars k
  rw [S.xIdeal_eq_range k]
  exact (C.cutX_mem_range a.val).mp a.property

theorem cutXRange_factor : C.cutXRangeProjection ≫ C.cutXRangeInclusion=C.cutX := rfl

noncomputable def cutXKernelSequence : ShortComplex (ModuleCat (S.CutPolynomialRing k)) :=
  ShortComplex.mk C.cutTerminalInclusion C.cutXRangeProjection C.cutTerminalInclusion_comp

noncomputable def cutXQuotientSequence : ShortComplex (ModuleCat (S.CutPolynomialRing k)) :=
  ShortComplex.mk C.cutXRangeInclusion C.cutHeadProjection C.cutXRangeInclusion_comp

theorem cutXKernelSequence_shortExact : C.cutXKernelSequence.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    refine ⟨⟨a,?_⟩,rfl⟩
    change S.xMultiply k (show S.TangentAlgebra k from a)=0
    exact congrArg Subtype.val ha
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    exact C.cutX.hom.surjective_rangeRestrict

theorem cutXQuotientSequence_shortExact : C.cutXQuotientSequence.ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    have hm : a ∈ S.xIdeal k := Ideal.Quotient.eq_zero_iff_mem.mp ha
    have hr : a ∈ (S.xMultiply k).range := by
      rw [← S.xIdeal_eq_range k]
      exact hm
    exact ⟨⟨a,(C.cutX_mem_range a).mpr hr⟩,rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (S.toHeadAlgebra k)
    exact Ideal.Quotient.mk_surjective
end NSP14.NumericalSemigroup.LinearCutData
