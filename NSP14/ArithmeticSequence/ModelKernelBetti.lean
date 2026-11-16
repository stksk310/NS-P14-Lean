module
public import NSP14.ArithmeticSequence.ModelPolynomialBetti
public import NSP14.ArithmeticSequence.WindowBetti
public import Mathlib.RingTheory.Noetherian.Basic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

noncomputable abbrev modelKernelFull : ModuleCat (VariableRing k (Fin D.v)) :=
  D.modelFullRestricted hv k (D.modelKernelNative hv k)

noncomputable def modelKernelNativeInclusion : D.modelKernelNative hv k ⟶ D.modelRegularNative hv k :=
  ModuleCat.ofHom (D.modelKernel hv k).subtype

noncomputable def modelKernelFullInclusion : D.modelKernelFull hv k ⟶ D.modelRegularFull hv k :=
  (ModuleCat.restrictScalars (D.modelFullPolynomial hv k).toRingHom).map (D.modelKernelNativeInclusion hv k)

noncomputable instance modelKernelFullFinite :
    Module.Finite (VariableRing k (Fin D.v)) (D.modelKernelFull hv k) := by
  apply Module.Finite.of_injective (D.modelKernelFullInclusion hv k).hom
  intro a b h
  exact Subtype.ext h

/-- Every remaining variable action is retained when regular x is
removed from the actual full-variable complex of the actual ideal J. -/
noncomputable def modelKernelFullHomologyIso (i : ℕ) :
    koszulHomologyK k (Fin D.v) (D.modelKernelFull hv k) i ≅
      koszulHomologyK k (Fin (D.v-1)) (D.modelWindowModule hv k) i :=
  (D.modelFullNativeHomologyIso hv k (D.modelKernelNative hv k) i).symm ≪≫
    regularModulePolynomialReductionIso ((D.ordinaryModel hv).source.TangentAlgebra k)
      ((D.ordinaryModel hv).source.xElement k) (D.modelKernelNative hv k) k (Fin (D.v-1))
      (D.modelWindowPolynomial hv k) (D.modelKernelX_injective hv k) i

theorem modelKernelFull_betti_eq_window (i : ℕ) :
    totalBetti k (Fin D.v) (D.modelKernelFull hv k) i=
      totalBetti k (Fin (D.v-1)) (D.modelWindowModule hv k) i :=
  (D.modelKernelFullHomologyIso hv k i).toLinearEquiv.finrank_eq

/-- Intrinsic ordinary Tor of the actual kernel, not only its finite
window, has the computed table. No k-finiteness of J is assumed. -/
theorem modelKernelFull_betti [Infinite k] (i : ℕ) :
    totalBetti k (Fin D.v) (D.modelKernelFull hv k) i=
      if i+1≤D.residueDefect then (D.residueDefect-i)*D.v.choose i
      else (i+1-D.residueDefect)*D.v.choose (i+1) := by
  rw [D.modelKernelFull_betti_eq_window,D.modelWindow_betti]
end NSP14.ArithmeticSequence.Data
