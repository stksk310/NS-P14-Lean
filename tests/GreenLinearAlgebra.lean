module
public import NSP14
@[expose] public section
namespace GreenLinearAlgebra
open scoped BigOperators
theorem independent_line (k V : Type) [Field k] [Infinite k] [AddCommGroup V] [Module k V]
    {ι : Type} [Fintype ι] (u v : ι → V) (hu : LinearIndependent k u) :
    ∃ t : k, t ≠ 0 ∧ LinearIndependent k (fun i => u i + t • v i) :=
  NSP14.Green.generic_independent_line u v hu

end GreenLinearAlgebra
