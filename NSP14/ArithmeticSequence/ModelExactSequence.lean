module
public import NSP14.ArithmeticSequence.ModelKernelBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable abbrev modelHeadNative : ModuleCat ((D.ordinaryModel hv).source.TangentAlgebra k) :=
  (ModuleCat.restrictScalars (D.modelToHead hv k).toRingHom).obj (ModuleCat.of (D.source.HeadAlgebra k) (D.source.HeadAlgebra k))

noncomputable def modelNativeToHead : D.modelRegularNative hv k ⟶ D.modelHeadNative hv k :=
  ModuleCat.ofHom (X:=D.modelRegularNative hv k) (Y:=D.modelHeadNative hv k)
    { toFun := D.modelToHead hv k
      map_add' := (D.modelToHead hv k).map_add
      map_smul' := (D.modelToHead hv k).map_mul }

theorem modelNative_comp : D.modelKernelNativeInclusion hv k ≫ D.modelNativeToHead hv k=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change D.modelToHead hv k a.val=0
  exact a.property

noncomputable def modelNativeSequence : ShortComplex (ModuleCat ((D.ordinaryModel hv).source.TangentAlgebra k)) :=
  ShortComplex.mk (D.modelKernelNativeInclusion hv k) (D.modelNativeToHead hv k) (D.modelNative_comp hv k)

theorem modelNativeSequence_shortExact : (D.modelNativeSequence hv k).ShortExact := by
  unfold modelNativeSequence
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    change D.modelToHead hv k a=0 at ha
    exact ⟨⟨a,ha⟩,rfl⟩
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    change Function.Surjective (D.modelToHead hv k)
    exact D.modelToHead_surjective hv k

noncomputable abbrev modelHeadFull : ModuleCat (VariableRing k (Fin D.v)) :=
  D.modelFullRestricted hv k (D.modelHeadNative hv k)

noncomputable def modelFullSequence : ShortComplex (ModuleCat (VariableRing k (Fin D.v))) :=
  (D.modelNativeSequence hv k).map (ModuleCat.restrictScalars (D.modelFullPolynomial hv k).toRingHom)

theorem modelFullSequence_shortExact : (D.modelFullSequence hv k).ShortExact := by
  have h := D.modelNativeSequence_shortExact hv k
  let : Mono (D.modelNativeSequence hv k).f := h.mono_f
  let : Epi (D.modelNativeSequence hv k).g := h.epi_g
  exact h.map _

noncomputable instance modelHeadFullFinite :
    Module.Finite (VariableRing k (Fin D.v)) (D.modelHeadFull hv k) := by
  let f : D.modelRegularFull hv k ⟶ D.modelHeadFull hv k :=
    (ModuleCat.restrictScalars (D.modelFullPolynomial hv k).toRingHom).map (D.modelNativeToHead hv k)
  apply Module.Finite.of_surjective f.hom
  change Function.Surjective (D.modelToHead hv k)
  exact D.modelToHead_surjective hv k
end NSP14.ArithmeticSequence.Data
