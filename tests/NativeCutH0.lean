module
public import NSP14.Ordinary.NativeFullTransfer
public import tests.CutResidual
public import tests.ActualTorRow
@[expose] public section
open CategoryTheory NSP14 NSP14.Homological
namespace NativeCutH0Acceptance
noncomputable abbrev C := CutResidualAcceptance.C
noncomputable abbrev W := ActualTorRowAcceptance.W2
abbrev L := InfiniteScalarField (ZMod 2)

theorem actual_h0_Z_model : Nonempty (C.nativeCutH0Z ≅ firstOrderModule L C.complementRank 0) :=
  ⟨C.nativeCutH0ZIso⟩

theorem actual_h0_Z_betti_one :
    letI := C.nativeCutH0Z_finite
    totalBetti L (Fin C.complementRank) C.nativeCutH0Z 1=3 := by
  let := C.nativeCutH0Z_finite
  rw [C.nativeCutH0Z_betti 1 (by decide),CutResidualAcceptance.complement]
  norm_num

theorem actual_R_complex : Nonempty (W.cut.nativeCoefficientCutComplex ≅
    (coefficientKoszulListFunctor L (Option (Fin W.source.actualCutRank)) W.relativeVariableOrder).obj W.relativeG) :=
  ⟨W.relativeNativeKoszulIso⟩

theorem actual_corrected_comparison (i : ℕ) :
    letI := W.relativeG_finite
    Module.finrank L (W.cut.nativeExtendedCoefficientComplex.homology i) ≤
        (if i=0 then 1 else i*(W.cut.complementRank+1).choose (i+1))+
          binomialTransform W.cut.complementRank
            (fun j => if j=0 then 0 else totalBetti L (Option (Fin W.source.actualCutRank)) W.relativeG j) i :=
  W.nativeFull_corrected_bound i
end NativeCutH0Acceptance
