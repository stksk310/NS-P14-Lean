module

public import NSP14.Homological.Betti
public import NSP14.Homological.ActualKoszulTransport

@[expose] public section

open CategoryTheory
open NSP14.Homological

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type) [Field k]

noncomputable instance formalGFullPolynomialFinite :
    Module.Finite (S.FullPolynomialRing k) (S.FormalTangentAlgebra k) :=
  Module.Finite.equiv (S.completedPolynomialLinearEquiv k)

/-- The completed cone comparison transports ordinary derived Tor over the full e-variable ring. -/
noncomputable def completedTorIso (i : ℕ) :
    (((CategoryTheory.Tor (ModuleCat (S.FullPolynomialRing k)) i).obj
      (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k))).obj
        (residueField k S.AtomExponent)) ≅
    (((CategoryTheory.Tor (ModuleCat (S.FullPolynomialRing k)) i).obj
      (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k))).obj
        (residueField k S.AtomExponent)) :=
  ((CategoryTheory.Tor (ModuleCat (S.FullPolynomialRing k)) i).mapIso
    (S.completedPolynomialLinearEquiv k).toModuleIso).app _

theorem completed_totalBetti (i : ℕ) :
    totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i =
      totalBetti k S.AtomExponent (ModuleCat.of (S.FullPolynomialRing k) (S.FormalTangentAlgebra k)) i :=
  totalBetti_iso k S.AtomExponent (S.completedPolynomialLinearEquiv k).toModuleIso i

/-- Same-jump strata transport ordinary Tor over S₀, keeping the quotient and variable set. -/
noncomputable def jumpStratumTorIso (s : ℕ) (hs : 0<s) (i : ℕ) :
    (((CategoryTheory.Tor (ModuleCat (S.PolynomialRing k)) i).obj
      (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s))).obj
        (residueField k S.NonXAtom)) ≅
    (((CategoryTheory.Tor (ModuleCat (S.PolynomialRing k)) i).obj
      (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s))).obj
        (residueField k S.NonXAtom)) :=
  ((CategoryTheory.Tor (ModuleCat (S.PolynomialRing k)) i).mapIso
    (S.jumpStratumEquiv k s hs).toModuleIso).app _

noncomputable instance descendingStratumPolynomialFinite (s : ℕ) :
    Module.Finite (S.PolynomialRing k) (S.DescendingJumpStratum k s) := by
  unfold DescendingJumpStratum
  infer_instance

noncomputable instance ascendingStratumPolynomialFinite (s : ℕ) :
    Module.Finite (S.PolynomialRing k) (S.AscendingJumpStratum k s) := by
  unfold AscendingJumpStratum
  infer_instance

theorem jumpStratum_totalBetti (s : ℕ) (hs : 0<s) (i : ℕ) :
    totalBetti k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s)) i =
      totalBetti k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s)) i :=
  totalBetti_iso k S.NonXAtom (S.jumpStratumEquiv k s hs).toModuleIso i

/-- Homology finiteness for actual G is obtained over the full minimal presentation. -/
theorem actualG_homology_finite (i : ℕ) : Module.Finite k
    (koszulHomologyK k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i) :=
  koszul_homology_finite k S.AtomExponent _ i

end NSP14.NumericalSemigroup
