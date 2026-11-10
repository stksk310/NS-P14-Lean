module
import NSP14
open NSP14.Homological CategoryTheory
variable (k σ : Type) [Field k]
example (xs : List σ) (S : ShortComplex (ModuleCat.{0} (VariableRing k σ))) (hS : S.ShortExact) :
    (S.map (koszulFunctor k σ xs)).ShortExact := koszul_shortExact k σ xs S hS
