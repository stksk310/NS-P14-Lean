module
public import NSP14.ArithmeticSequence.ModelWindowAction
public import tests.ArithmeticSequenceConeBetti
@[expose] public section
open NSP14 NSP14.Homological
namespace APKernelWindowAcceptance
abbrev D := ArithmeticSequenceConeBettiAcceptance.mixed

theorem actual_window_finite :
    Module.Finite (ZMod 2)
      ((ModuleCat.restrictScalars (algebraMap (ZMod 2)
        ((D.ordinaryModel (by decide)).source.TangentAlgebra (ZMod 2)))).obj
        (D.modelNativeQuotient (by decide) (ZMod 2))) := inferInstance

theorem actual_lower_to_upper :
    D.modelMonomial (by decide) (ZMod 2) 2 • D.modelWindowClass (by decide) (ZMod 2) 0=
      D.modelWindowClass (by decide) (ZMod 2) 2 := by
  rw [D.modelWindowClass_twoStep (by decide) (ZMod 2) 0 2 (by decide) (by decide) (by decide)]
  rw [ite_eq_left (by decide)]

theorem actual_other_lower_to_upper :
    D.modelMonomial (by decide) (ZMod 2) 1 • D.modelWindowClass (by decide) (ZMod 2) 1=
      D.modelWindowClass (by decide) (ZMod 2) 2 := by
  rw [D.modelWindowClass_twoStep (by decide) (ZMod 2) 1 1 (by decide) (by decide) (by decide)]
  rw [ite_eq_left (by decide)]

theorem actual_upper_killed :
    D.modelMonomial (by decide) (ZMod 2) 1 • D.modelWindowClass (by decide) (ZMod 2) 2=0 := by
  rw [D.modelWindowClass_twoStep (by decide) (ZMod 2) 2 1 (by decide) (by decide) (by decide)]
  rw [ite_eq_right (by decide)]

theorem actual_regular_kernel_reduction (rs : List ((D.ordinaryModel (by decide)).source.TangentAlgebra (ZMod 2))) (i : ℕ) :
    Nonempty
      ((actionCoefficientComplex (ZMod 2) ((D.ordinaryModel (by decide)).source.TangentAlgebra (ZMod 2))
        (((D.ordinaryModel (by decide)).source.xElement (ZMod 2))::rs)
        (D.modelKernelNative (by decide) (ZMod 2))).homology i ≅
      (actionCoefficientComplex (ZMod 2) ((D.ordinaryModel (by decide)).source.TangentAlgebra (ZMod 2))
        rs (D.modelNativeQuotient (by decide) (ZMod 2))).homology i) :=
  ⟨D.modelKernelReductionIso (by decide) (ZMod 2) rs i⟩
end APKernelWindowAcceptance
