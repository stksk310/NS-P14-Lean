module
public import NSP14.Homological.VariableIdealBetti
@[expose] public section
namespace NSP14.Tests.VariableIdealBetti
theorem actual_coordinate_betti (k σ : Type) [Field k] [Fintype σ]
    (xs : List σ) (hx : xs.Nodup) (i : ℕ) :
    Homological.totalBetti k σ
      (ModuleCat.of (Homological.VariableRing k σ)
        ((Homological.VariableRing k σ) ⧸ Homological.variablesIdeal k σ xs)) i=
      xs.length.choose i :=
  Homological.variable_ideal_betti k σ xs hx i
end NSP14.Tests.VariableIdealBetti
