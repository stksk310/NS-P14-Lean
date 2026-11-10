module
public import audit.run15_apcone.ClosedGoals
public import NSP14.ArithmeticSequence.ModelWindowAction
public import NSP14.Homological.TwoStepBetti
@[expose] public section
open CategoryTheory NSP14 NSP14.Homological
namespace Run15APFoundations

/-- Actual native quotient, arbitrary original coefficient field. No
finite dimension of B or J is assumed. -/
theorem native_quotient_finite (D : ArithmeticSequence.Data) (hv : 2 ≤ D.v)
    (k : Type) [Field k] :
    Module.Finite k ((ModuleCat.restrictScalars (algebraMap k
      ((D.ordinaryModel hv).source.TangentAlgebra k))).obj (D.modelNativeQuotient hv k)) :=
  D.modelNativeQuotientCoefficientFinite hv k

/-- This audit certifies the actual kernel reduction; it does not claim
the remaining APBettiGoal or a vanishing Tor map from a degree slogan. -/
noncomputable def actual_kernel_reduction (D : ArithmeticSequence.Data) (hv : 2 ≤ D.v)
    (k : Type) [Field k] (rs : List ((D.ordinaryModel hv).source.TangentAlgebra k)) (i : ℕ) :
    (actionCoefficientComplex k ((D.ordinaryModel hv).source.TangentAlgebra k)
      (((D.ordinaryModel hv).source.xElement k)::rs) (D.modelKernelNative hv k)).homology i ≅
    (actionCoefficientComplex k ((D.ordinaryModel hv).source.TangentAlgebra k)
      rs (D.modelNativeQuotient hv k)).homology i :=
  D.modelKernelReductionIso hv k rs i
end Run15APFoundations
