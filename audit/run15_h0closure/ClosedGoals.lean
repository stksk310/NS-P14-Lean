module
public import audit.run15_bclosure.ClosedGoals
public import NSP14.Ordinary.NativeFullTransfer
@[expose] public section
open CategoryTheory NSP14 NSP14.Homological
namespace Run15H0Closure

/-- The native complex is the actual relative R Koszul complex with all
complement variables then applied. This is not yet intrinsic full Tor. -/
theorem native_corrected_comparison {k : Type} [Field k] (W : Ordinary.ActualWitness k) (i : ℕ) :
    letI := W.relativeG_finite
    Module.finrank (InfiniteScalarField k) (W.cut.nativeExtendedCoefficientComplex.homology i) ≤
      (if i=0 then 1 else i*(W.cut.complementRank+1).choose (i+1))+
        binomialTransform W.cut.complementRank
          (fun j => if j=0 then 0 else totalBetti (InfiniteScalarField k)
            (Option (Fin W.source.actualCutRank)) W.relativeG j) i := W.nativeFull_corrected_bound i

/-- Native H0, with the actual inherited Z action, rather than a vector
space with the same dimension. -/
theorem actual_H0_Z_model {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k) :
    Nonempty (C.nativeCutH0Z ≅ firstOrderModule k C.complementRank 0) := ⟨C.nativeCutH0ZIso⟩
end Run15H0Closure
