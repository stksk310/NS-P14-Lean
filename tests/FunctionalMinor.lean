module
public import NSP14
@[expose] public section
namespace FunctionalMinorAcceptance
open NSP14.Homological
variable (k I X Y : Type) [Field k] [Fintype I] [DecidableEq I]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y] [Module.Finite k Y]
theorem actual_map_rank (d : X →ₗ[k] Y) (columns : I → X) (rows : I → Y →ₗ[k] k)
    (h : Matrix.det (fun i j => rows i (d (columns j))) ≠ 0) :
    Fintype.card I ≤ Module.finrank k d.range := functional_minor_rank_lower_bound k d columns rows h
end FunctionalMinorAcceptance
