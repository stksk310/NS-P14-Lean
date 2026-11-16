module
public import NSP14.Endpoint.NativeTransfer
public import NSP14.Endpoint.QuotientBound
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory CategoryTheory.Limits NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

noncomputable instance QCoreCoefficientFinite : Module.Finite k (coefficientModule k D.a (D.QCoreModule k)) :=
  regularRestriction_coefficientFinite k D.a _ _

noncomputable instance QActualCoefficientFinite : Module.Finite k (coefficientModule k D.a (D.QActualModule k)) :=
  regularRestriction_coefficientFinite k D.a _ _

noncomputable def QKernelModule : ModuleCat (D.InternalRing k) :=
  ModuleCat.of (D.InternalRing k) (D.QCoreToActualModule k).hom.ker

noncomputable def QKernelInclusion : D.QKernelModule k ⟶ D.QCoreModule k :=
  ModuleCat.ofHom (X:=D.QKernelModule k) (Y:=D.QCoreModule k) (D.QCoreToActualModule k).hom.ker.subtype

noncomputable def QKernelCoefficientInclusion : coefficientModule k D.a (D.QKernelModule k) ⟶
    coefficientModule k D.a (D.QCoreModule k) :=
  (ModuleCat.restrictScalars (algebraMap k (D.InternalRing k))).map (D.QKernelInclusion k)

theorem QKernelCoefficientInclusion_injective : Function.Injective (D.QKernelCoefficientInclusion k).hom :=
  fun _a _b h => Subtype.ext h

noncomputable instance QKernelCoefficientFinite : Module.Finite k (coefficientModule k D.a (D.QKernelModule k)) :=
  Module.Finite.of_injective (D.QKernelCoefficientInclusion k).hom (D.QKernelCoefficientInclusion_injective k)

noncomputable instance QKernelModuleFinite : Module.Finite (D.InternalRing k) (D.QKernelModule k) :=
  polynomialFinite_of_coefficientFinite _

noncomputable def QKernelSequence : ShortComplex (ModuleCat (D.InternalRing k)) :=
  ShortComplex.mk (D.QKernelInclusion k) (D.QCoreToActualModule k) (by
    apply ModuleCat.hom_ext
    ext a
    exact a.property)

theorem QKernelSequence_shortExact : (D.QKernelSequence k).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact Submodule.range_subtype _
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    exact D.QCoreToActual_surjective k

noncomputable def QCoreCoefficientEquiv : coefficientModule k D.a (D.QCoreModule k) ≃ₗ[k] D.QCore k :=
  regularRestrictionCoefficientEquiv k D.a _ _

noncomputable def QActualCoefficientEquiv : coefficientModule k D.a (D.QActualModule k) ≃ₗ[k] D.QActual k :=
  regularRestrictionCoefficientEquiv k D.a _ _

theorem QKernel_dimension_add :
    Module.finrank k (coefficientModule k D.a (D.QKernelModule k))+D.actualP k=D.coreP k := by
  let S := (D.QKernelSequence k).map (ModuleCat.restrictScalars (algebraMap k (D.InternalRing k)))
  let : Mono (D.QKernelSequence k).f := (D.QKernelSequence_shortExact k).mono_f
  let : Epi (D.QKernelSequence k).g := (D.QKernelSequence_shortExact k).epi_g
  have hS : S.ShortExact := (D.QKernelSequence_shortExact k).map _
  let : Module.Finite k S.X₂ := D.QCoreCoefficientFinite k
  have h := exact_rank_sum k S hS.exact
  have hinj : Function.Injective S.f.hom := D.QKernelCoefficientInclusion_injective k
  have hsurj : Function.Surjective S.g.hom := D.QCoreToActual_surjective k
  rw [LinearMap.finrank_range_of_inj hinj,LinearMap.range_eq_top.mpr hsurj,finrank_top] at h
  change Module.finrank k (coefficientModule k D.a (D.QKernelModule k))+
    Module.finrank k (coefficientModule k D.a (D.QActualModule k))=
      Module.finrank k (coefficientModule k D.a (D.QCoreModule k)) at h
  rw [(D.QCoreCoefficientEquiv k).finrank_eq,(D.QActualCoefficientEquiv k).finrank_eq] at h
  exact h

theorem QKernel_dimension : Module.finrank k (coefficientModule k D.a (D.QKernelModule k))=D.coreP k-D.actualP k := by
  have h := D.QKernel_dimension_add k
  omega

theorem actualP_le_coreP : D.actualP k≤D.coreP k := by
  have h := D.QKernel_dimension_add k
  omega

/-- The compensation is proved using the real quotient and its real
kernel, with the actual LES and finite-k kernel chain bound. -/
theorem actual_kernel_compensation (i : ℕ) : totalBetti k D.a (D.QActualModule k) i≤
    totalBetti k D.a (D.QCoreModule k) i+(if i=0 then 0 else (D.coreP k-D.actualP k)*D.q.choose (i-1)) := by
  cases i with
  | zero =>
    simp only [ite_true,add_zero]
    let : Epi (D.QCoreToActualModule k) := (ModuleCat.epi_iff_surjective _).mpr (D.QCoreToActual_surjective k)
    exact totalBetti_zero_le_of_epi k D.a (D.QCoreToActualModule k)
  | succ i =>
    let : Module.Finite (D.InternalRing k) (D.QKernelSequence k).X₁ := D.QKernelModuleFinite k
    let : Module.Finite (D.InternalRing k) (D.QKernelSequence k).X₂ := D.QCoreModuleFinite k
    let : Module.Finite (D.InternalRing k) (D.QKernelSequence k).X₃ := D.QActualModuleFinite k
    have h := NSP14.Endpoint.quotient_betti_bound k D.a (D.QKernelSequence k) (D.QKernelSequence_shortExact k) i
    change totalBetti k D.a (D.QActualModule k) (i+1)≤
      totalBetti k D.a (D.QCoreModule k) (i+1)+totalBetti k D.a (D.QKernelModule k) i at h
    have hb := NSP14.Endpoint.finite_betti_bound k D.a (D.QKernelModule k) i
    rw [D.QKernel_dimension,Fintype.card_coe] at hb
    change totalBetti k D.a (D.QKernelModule k) i≤(D.coreP k-D.actualP k)*D.q.choose i at hb
    simpa only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel] using
      h.trans (Nat.add_le_add_left hb (totalBetti k D.a (D.QCoreModule k) (i+1)))
end NSP14.Endpoint.Data
