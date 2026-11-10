module

public import NSP14.Homological.KoszulNaturality
public import NSP14.Homological.PolynomialModules

@[expose] public section

open CategoryTheory

namespace NSP14.NumericalSemigroup

open NSP14.Homological

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

/-- The natural completed tangent-cone comparison is transported as an actual e-variable complex iso. -/
noncomputable def completedKoszulIso (xs : List S.AtomExponent) :
    (koszulFunctor k S.AtomExponent xs).obj (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) ≅
      (koszulFunctor k S.AtomExponent xs).obj (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) :=
  (koszulFunctor k S.AtomExponent xs).mapIso (S.completedPolynomialLinearEquiv k).toModuleIso

noncomputable def completedKoszulHomologyIso (xs : List S.AtomExponent) (i : ℕ) :
    (koszulHomologyFunctor k S.AtomExponent xs i).obj (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) ≅
      (koszulHomologyFunctor k S.AtomExponent xs i).obj (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) :=
  (koszulHomologyFunctor k S.AtomExponent xs i).mapIso (S.completedPolynomialLinearEquiv k).toModuleIso

/-- This transport keeps the S₀ variable set separate from the full source presentation. -/
noncomputable def completedNonXKoszulHomologyIso (xs : List S.NonXAtom) (i : ℕ) :
    (koszulHomologyFunctor k S.NonXAtom xs i).obj (ModuleCat.of (S.PolynomialRing k) (S.TangentAlgebra k)) ≅
      (koszulHomologyFunctor k S.NonXAtom xs i).obj (ModuleCat.of (S.PolynomialRing k) (S.FormalTangentAlgebra k)) :=
  (koszulHomologyFunctor k S.NonXAtom xs i).mapIso (S.completedNonXPolynomialLinearEquiv k).toModuleIso

/-- Only the same-jump quotient equivalence is transported, never a global T≅N module assertion. -/
noncomputable def jumpStratumKoszulIso (xs : List S.NonXAtom) (s : ℕ) (hs : 0<s) :
    (koszulFunctor k S.NonXAtom xs).obj (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s)) ≅
      (koszulFunctor k S.NonXAtom xs).obj (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s)) :=
  (koszulFunctor k S.NonXAtom xs).mapIso (S.jumpStratumEquiv k s hs).toModuleIso

noncomputable def jumpStratumKoszulHomologyIso (xs : List S.NonXAtom) (s : ℕ) (hs : 0<s) (i : ℕ) :
    (koszulHomologyFunctor k S.NonXAtom xs i).obj (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s)) ≅
      (koszulHomologyFunctor k S.NonXAtom xs i).obj (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s)) :=
  (koszulHomologyFunctor k S.NonXAtom xs i).mapIso (S.jumpStratumEquiv k s hs).toModuleIso

end NSP14.NumericalSemigroup
