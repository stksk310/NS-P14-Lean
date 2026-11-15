module
public import NSP14.Homological.TriangularBlockRank
@[expose] public section
open scoped BigOperators
namespace NSP14.Tests.TriangularBlockRank
theorem actual_block_rank (k ι X Y : Type) [Field k] [Fintype ι] [LinearOrder ι]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
    (d : X →ₗ[k] Y) (U : ι → Submodule k X) (P : ι → Y →ₗ[k] Y)
    (htri : ∀ a b, b<a → ∀ x : U b,P a (d x)=0) :
    (∑ a,Module.finrank k ((P a).comp (d.comp (U a).subtype)).range) ≤ Module.finrank k d.range :=
  Homological.triangular_block_rank k d U P htri
end NSP14.Tests.TriangularBlockRank
