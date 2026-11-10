module
public import tests.Run13Fixtures
@[expose] public section
namespace Run13BaseChange
open NSP14.Homological CategoryTheory
open scoped TensorProduct
variable (k L : Type) [Field k] [Field L] [Algebra k L]
noncomputable def actual_polynomial_base_change : L ⊗[k] VariableRing k (Fin 2) ≃ₐ[L] VariableRing L (Fin 2) :=
  polynomialFieldExtension k L (Fin 2)
theorem square_extended_complex_dimension (i : ℕ) :
    Module.finrank L ((((fieldExtension k L).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (coefficientKoszulComplex k (Fin 1) (Run13Fixtures.squareModule k))).homology i) =
        totalBetti k (Fin 1) (Run13Fixtures.squareModule k) i :=
  extendedCoefficientKoszul_finrank k (Fin 1) L _ i
theorem char_two_infinite_extension (i : ℕ) :
    Module.finrank (RatFunc (ZMod 2))
      ((((fieldExtension (ZMod 2) (RatFunc (ZMod 2))).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (coefficientKoszulComplex (ZMod 2) (Fin 1) (Run13Fixtures.squareModule (ZMod 2)))).homology i) =
          totalBetti (ZMod 2) (Fin 1) (Run13Fixtures.squareModule (ZMod 2)) i :=
  extendedCoefficientKoszul_finrank (ZMod 2) (Fin 1) (RatFunc (ZMod 2)) _ i
end Run13BaseChange
