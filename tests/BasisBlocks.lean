module
public import NSP14.Homological.BasisBlocks
@[expose] public section
namespace NSP14.Tests.BasisBlocks
theorem actual_basis_diagonal_rank (k I J Γ X Y : Type) [Field k]
    [Fintype I] [Fintype J] [Fintype Γ] [LinearOrder Γ]
    [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]
    (b : Module.Basis I k X) (c : Module.Basis J k Y) (u : I → Γ) (v : J → Γ)
    (d : X →ₗ[k] Y) (htri : ∀ i j,u i<v j → c.repr (d (b i)) j=0) :
    Module.finrank k (Homological.basisDiagonalMap k b u c v d).range ≤ Module.finrank k d.range :=
  Homological.basisDiagonalMap_rank k b u c v d htri
end NSP14.Tests.BasisBlocks
