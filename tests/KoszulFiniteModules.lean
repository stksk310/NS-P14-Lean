module
public import tests.Run13Fixtures
@[expose] public section
namespace Run13Finite
open NSP14 NSP14.NumericalSemigroup NSP14.Homological
variable (S : NumericalSemigroup) (k : Type) [Field k]
theorem G_finite (i : ℕ) : Module.Finite k (koszulHomologyK k S.AtomExponent
    (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i) := S.actualG_homology_finite k i
theorem T_finite (i : ℕ) : Module.Finite k (koszulHomologyK k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) ((S.xMultiply k).ker)) i) := koszul_homology_finite k S.NonXAtom _ i
theorem A_finite (i : ℕ) : Module.Finite k (koszulHomologyK k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) (S.HeadAlgebra k)) i) := koszul_homology_finite k S.NonXAtom _ i
theorem N_finite (i : ℕ) : Module.Finite k (koszulHomologyK k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) ((S.nonAperyIdeal k).restrictScalars k)) i) :=
  koszul_homology_finite k S.NonXAtom _ i
theorem Q_finite (i : ℕ) : Module.Finite k (koszulHomologyK k S.NonXAtom
    (ModuleCat.of (S.PolynomialRing k) (S.AperyAlgebra k)) i) := koszul_homology_finite k S.NonXAtom _ i
/-- Regression against applying finite-dimensional rank-nullity to the polynomial chain groups. -/
theorem polynomial_not_finite_over_coefficients : ¬Module.Finite k (Run13Fixtures.P1 k) := by
  intro h
  let : Module.Finite k (Run13Fixtures.P1 k) := h
  let : Finite (Fin 1 →₀ ℕ) := Module.Finite.finite_basis (MvPolynomial.basisMonomials (Fin 1) k)
  have hi : Function.Injective (fun n : ℕ => Finsupp.single (0 : Fin 1) n) := by
    intro a b he
    simpa using congrArg (fun f : Fin 1 →₀ ℕ => f 0) he
  have : Finite ℕ := Finite.of_injective _ hi
  exact not_finite ℕ
end Run13Finite
