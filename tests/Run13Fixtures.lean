module

public import NSP14
public import tests.Run12Fixtures
public import tests.Run12BasicExamples
public import tests.PolynomialAction
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.RatFunc.Basic

@[expose] public section

namespace Run13Fixtures
open NSP14.Homological

instance primeTwo : Fact (Nat.Prime 2) := ⟨by decide⟩

abbrev P1 (k : Type) [Field k] := VariableRing k (Fin 1)

noncomputable def squareIdeal (k : Type) [Field k] : Ideal (P1 k) :=
  Ideal.span {(MvPolynomial.X (0 : Fin 1))^2}

noncomputable def squareModule (k : Type) [Field k] : ModuleCat (P1 k) :=
  ModuleCat.of (P1 k) (P1 k ⧸ squareIdeal k)

noncomputable instance squareModuleFinite (k : Type) [Field k] : Module.Finite (P1 k) (squareModule k) :=
  inferInstanceAs (Module.Finite (P1 k) (P1 k ⧸ squareIdeal k))

end Run13Fixtures
