module
public import NSP14
@[expose] public section
open NSP14
namespace CutPolynomialInjectionAcceptance
variable (S : NumericalSemigroup) (k : Type) [Field k] (C : S.LinearCutData k)
theorem actual_P_subring : Function.Injective C.toPolynomialRing := C.toPolynomialRing_injective
end CutPolynomialInjectionAcceptance
