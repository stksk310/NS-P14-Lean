module
public import tests.Run13Fixtures
@[expose] public section
namespace Run13Tor
open NSP14.Homological CategoryTheory
variable (k : Type) [Field k]
noncomputable def polynomial_resolution := koszulResolution k (Fin 2)
noncomputable def square_tor (i : ℕ) := torKoszulIso k (Fin 1) (Run13Fixtures.squareModule k) i
noncomputable def char_two_tor (M : ModuleCat (VariableRing (ZMod 2) (Fin 2))) (i : ℕ) :=
  torKoszulIso (ZMod 2) (Fin 2) M i
noncomputable def char_two_contraction (M : ModuleCat (VariableRing (ZMod 2) (Fin 2))) (x : Fin 2) :=
  koszulVariableHomotopy (ZMod 2) (Fin 2) M x
theorem char_two_free_betti : totalBetti (ZMod 2) (Fin 2)
    (ModuleCat.of (VariableRing (ZMod 2) (Fin 2)) (VariableRing (ZMod 2) (Fin 2))) 0=1 :=
  totalBetti_free_zero (ZMod 2) (Fin 2)
end Run13Tor
