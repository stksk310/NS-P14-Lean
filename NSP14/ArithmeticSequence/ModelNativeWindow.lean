module
public import NSP14.ArithmeticSequence.ModelKernelShift
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable abbrev modelKernelNative : ModuleCat ((D.ordinaryModel hv).source.TangentAlgebra k) :=
  ModuleCat.of ((D.ordinaryModel hv).source.TangentAlgebra k) (D.modelKernel hv k)

noncomputable abbrev modelNativeQuotient :=
  scalarModuleQuotient ((D.ordinaryModel hv).source.TangentAlgebra k)
    ((D.ordinaryModel hv).source.xElement k) (D.modelKernelNative hv k)

noncomputable def modelNativeWindowIdentity :
    (ModuleCat.restrictScalars (algebraMap k ((D.ordinaryModel hv).source.TangentAlgebra k))).obj
      (D.modelNativeQuotient hv k) ≃ₗ[k]
        (D.modelKernel hv k ⧸ (D.modelKernelX hv k).range) := by
  let R := (D.ordinaryModel hv).source.TangentAlgebra k
  let p : Submodule R (D.modelKernel hv k) :=
    (((D.ordinaryModel hv).source.xElement k) • 𝟙 (D.modelKernelNative hv k)).hom.range
  have hp : p.restrictScalars k=(D.modelKernelX hv k).range := by
    ext a
    rfl
  let e := (Submodule.Quotient.restrictScalarsEquiv k p).symm.trans (Submodule.quotEquivOfEq _ _ hp)
  exact
    { toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' c a := by
        change e ((algebraMap k R c) • (show D.modelKernel hv k ⧸ p from a))=c • e a
        rw [algebraMap_smul]
        exact e.map_smul c a }

/-- A k-linear coordinate equivalence for the actual R-module quotient
J/xJ. Its R and future non-x polynomial actions remain the quotient ones. -/
noncomputable def modelNativeWindowEquiv :
    (ModuleCat.restrictScalars (algebraMap k ((D.ordinaryModel hv).source.TangentAlgebra k))).obj
      (D.modelNativeQuotient hv k) ≃ₗ[k] (Fin D.v → k) :=
  (D.modelNativeWindowIdentity hv k).trans (D.modelKernelWindowEquiv hv k)

theorem modelNativeWindowEquiv_mk (a : D.modelKernel hv k) :
    D.modelNativeWindowEquiv hv k (Submodule.Quotient.mk a)=
      (fun i : Fin D.v => (D.modelKernelNatBasis hv k).repr a i.val) := rfl

noncomputable instance modelNativeQuotientCoefficientFinite :
    Module.Finite k ((ModuleCat.restrictScalars (algebraMap k ((D.ordinaryModel hv).source.TangentAlgebra k))).obj
      (D.modelNativeQuotient hv k)) :=
  Module.Finite.equiv (D.modelNativeWindowEquiv hv k).symm

/-- Actual regular reduction for the kernel of the ordinary-to-AP
surjection, with every remaining native action retained. -/
noncomputable def modelKernelReductionIso (rs : List ((D.ordinaryModel hv).source.TangentAlgebra k)) (i : ℕ) :
    (actionCoefficientComplex k ((D.ordinaryModel hv).source.TangentAlgebra k)
      (((D.ordinaryModel hv).source.xElement k)::rs) (D.modelKernelNative hv k)).homology i ≅
    (actionCoefficientComplex k ((D.ordinaryModel hv).source.TangentAlgebra k)
      rs (D.modelNativeQuotient hv k)).homology i :=
  regularModuleCoefficientReductionIso ((D.ordinaryModel hv).source.TangentAlgebra k)
    ((D.ordinaryModel hv).source.xElement k) (D.modelKernelNative hv k) k rs
    (D.modelKernelX_injective hv k) i
end NSP14.ArithmeticSequence.Data
