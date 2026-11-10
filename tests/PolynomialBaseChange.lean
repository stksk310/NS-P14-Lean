module

public import NSP14
public import tests.Run13Fixtures

@[expose] public section
open CategoryTheory NSP14.Homological

namespace PolynomialBaseChangeAcceptance

abbrev k := ZMod 2
abbrev L := RatFunc k
abbrev P := VariableRing k (Fin 2)

/-- A nonhomogeneous module map in characteristic two; its actual Koszul square commutes. -/
theorem nonhomogeneous_naturality :
    ((polynomialBaseChangeFunctor k L (Fin 2)).mapHomologicalComplex _).map
      (koszulMap k (Fin 2) [0,1] (principalMultiply k (Fin 2) (1+MvPolynomial.X 0))) ≫
        (koszulPolynomialBaseChangeIso k L (Fin 2) [0,1] (ModuleCat.of P P)).hom =
    (koszulPolynomialBaseChangeIso k L (Fin 2) [0,1] (ModuleCat.of P P)).hom ≫
      koszulMap L (Fin 2) [0,1]
        ((polynomialBaseChangeFunctor k L (Fin 2)).map (principalMultiply k (Fin 2) (1+MvPolynomial.X 0))) :=
  koszulPolynomialBaseChangeIso_naturality k L (Fin 2) [0,1] _

theorem changing_actualG (i : ℕ) :
    totalBetti L Run12Fixtures.changing.AtomExponent
      (ModuleCat.of (Run12Fixtures.changing.FullPolynomialRing L) (Run12Fixtures.changing.TangentAlgebra L)) i =
    totalBetti k Run12Fixtures.changing.AtomExponent
      (ModuleCat.of (Run12Fixtures.changing.FullPolynomialRing k) (Run12Fixtures.changing.TangentAlgebra k)) i :=
  Run12Fixtures.changing.actualG_totalBetti_baseChange k L i

end PolynomialBaseChangeAcceptance
