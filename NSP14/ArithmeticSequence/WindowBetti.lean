module
public import NSP14.ArithmeticSequence.WindowHankel
public import NSP14.Homological.HankelModuleBetti
public import Mathlib.Data.Fintype.EquivFin
@[expose] public section
open NSP14.Homological
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (hv : 2 ≤ D.v) (k : Type) [Field k]

/-- The actual J/xJ module has the predicted all-row Betti table.
The displayed points are actual field elements, not a rank assumption. -/
theorem modelWindow_betti_with_points (points : Fin (D.v-1) → k)
    (hp : Function.Injective points) (i : ℕ) :
    totalBetti k (Fin (D.v-1)) (D.modelWindowModule hv k) i=
      if i+1≤D.residueDefect then (D.residueDefect-i)*D.v.choose i
      else (i+1-D.residueDefect)*D.v.choose (i+1) := by
  have hc : D.residueDefect+(D.v-D.residueDefect)=(D.v-1)+1 := by
    have h := D.residueDefect_le
    omega
  have h := hankelModule_betti k (D.v-1) (D.modelWindowModule hv k)
    D.residueDefect (D.v-D.residueDefect) (D.modelPairCoordinates hv k)
    points hp hc (D.modelWindowHankel hv k) D.residueDefect_pos i
  simpa only [Nat.sub_add_cancel (show 1 ≤ D.v by omega)] using h

/-- Unconditional over every infinite field, including same-characteristic
infinite extensions of finite fields. -/
theorem modelWindow_betti [Infinite k] (i : ℕ) :
    totalBetti k (Fin (D.v-1)) (D.modelWindowModule hv k) i=
      if i+1≤D.residueDefect then (D.residueDefect-i)*D.v.choose i
      else (i+1-D.residueDefect)*D.v.choose (i+1) := by
  let points : Fin (D.v-1) → k := fun j => Infinite.natEmbedding k j.val
  apply D.modelWindow_betti_with_points hv k points
  intro a b h
  exact Fin.ext ((Infinite.natEmbedding k).injective h)
end NSP14.ArithmeticSequence.Data
