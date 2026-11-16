module
public import NSP14
@[expose] public section
namespace OrdinaryTorAcceptance
open NSP14
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)
theorem actual_tower_kernel (s j : ℕ) (hs : 1 ≤ s) :
    C.cutKEuler s j ≤ C.cutHighEuler s (s+1) j+C.cutHighEuler (s+1) (s+1) (j+1) :=
  C.cutTower_kernel_le s hs j
end OrdinaryTorAcceptance
