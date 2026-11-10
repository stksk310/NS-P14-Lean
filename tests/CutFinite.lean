module
public import NSP14
@[expose] public section
open NSP14 NSP14.NumericalSemigroup
namespace CutFiniteAcceptance
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)
theorem finite_actual_A : Module.Finite (S.CutPolynomialRing k) C.cutA := C.cutA_finite
theorem finite_actual_T : Module.Finite (S.CutPolynomialRing k) C.cutT := C.cutT_finite
theorem finite_actual_high_coeff (s n : ℕ) :
    Module.Finite k (NSP14.Homological.coefficientModule k (Fin S.actualCutRank) (C.cutHigh s n)) :=
  C.cutHigh_coefficientFinite s n
end CutFiniteAcceptance
