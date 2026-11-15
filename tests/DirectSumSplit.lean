module
public import NSP14.Homological.DirectSumSplit
@[expose] public section
open CategoryTheory
namespace NSP14.Tests.DirectSumSplit
theorem actual_summand_splitting (k : Type) [Field k]
    (C : ℤ → ChainComplex (ModuleCat k) ℕ) (t : ℤ) :
    Homological.directSumInclusion k C t ≫ Homological.directSumProjection k C t=𝟙 (C t) :=
  Homological.directSumInclusion_projection k C t
end NSP14.Tests.DirectSumSplit
