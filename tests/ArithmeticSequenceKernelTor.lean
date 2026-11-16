module
public import NSP14.ArithmeticSequence.ModelTorClosure
public import NSP14.Homological.InfiniteScalarField
public import tests.ArithmeticSequenceConeBetti
@[expose] public section
open CategoryTheory HomologicalComplex NSP14 NSP14.Homological
namespace ArithmeticSequenceKernelTorAcceptance
abbrev D := ArithmeticSequenceConeBettiAcceptance.mixed
abbrev K := InfiniteScalarField (ZMod 2)

theorem actual_kernel_zero : totalBetti K (Fin D.v) (D.modelKernelFull (by decide) K) 0=2 := by
  rw [D.modelKernelFull_betti]
  decide

theorem actual_kernel_first : totalBetti K (Fin D.v) (D.modelKernelFull (by decide) K) 1=3 := by
  rw [D.modelKernelFull_betti]
  decide

theorem actual_kernel_top : totalBetti K (Fin D.v) (D.modelKernelFull (by decide) K) 2=1 := by
  rw [D.modelKernelFull_betti]
  decide

/-- The ideal J has infinite k-chains. This all-row zero statement is
proved by an actual polynomial-variable factorization, not finite rank. -/
theorem actual_inclusion_zero (i : ℕ) :
    homologyMap ((coefficientKoszulFunctor (ZMod 2) (Fin D.v)).map
      (D.modelFullSequence (by decide) (ZMod 2)).f) i=0 :=
  D.modelKernelFull_homology_zero (by decide) (ZMod 2) i

theorem actual_LES_additivity (i : ℕ) :
    totalBetti (ZMod 2) (Fin D.v) (D.modelHeadFull (by decide) (ZMod 2)) (i+1)=
      totalBetti (ZMod 2) (Fin D.v) (D.modelRegularFull (by decide) (ZMod 2)) (i+1)+
        totalBetti (ZMod 2) (Fin D.v) (D.modelKernelFull (by decide) (ZMod 2)) i :=
  D.modelHeadFull_betti_add (by decide) (ZMod 2) i
end ArithmeticSequenceKernelTorAcceptance
