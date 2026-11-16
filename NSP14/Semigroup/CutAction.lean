module

public import NSP14.Semigroup.LinearForms
public import NSP14.Semigroup.JumpStrata
public import NSP14.Homological.InfiniteScalarField
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type) [Field k]

/-- P has r formal independent variables; its image inside A can have relations. -/
abbrev CutPolynomialRing := MvPolynomial (Fin S.actualCutRank) k

namespace LinearCutData

variable {S k} (C : S.LinearCutData k)

noncomputable def toPolynomialRing : S.CutPolynomialRing k →ₐ[k] S.PolynomialRing k :=
  MvPolynomial.aeval C.polynomialForm

theorem toPolynomialRing_X (i : Fin S.actualCutRank) :
    C.toPolynomialRing (MvPolynomial.X i) = C.polynomialForm i := MvPolynomial.aeval_X _ _

theorem polynomialForms_independent : LinearIndependent k C.polynomialForm := by
  have h := C.independent.map' (S.headDegree k 1).subtype (Submodule.ker_subtype _)
  have he : (fun i => (S.polynomialToA k).toLinearMap (C.polynomialForm i)) =
      (fun i => (C.forms i).val) := funext (fun i => C.polynomialForm_image i)
  change LinearIndependent k (fun i => (C.forms i).val) at h
  rw [← he] at h
  exact LinearIndependent.of_comp (S.polynomialToA k).toLinearMap h

/-- Restrict the actual S₀ action through the single fixed polynomial map. -/
noncomputable def restrictFunctor : ModuleCat (S.PolynomialRing k) ⥤ ModuleCat (S.CutPolynomialRing k) :=
  ModuleCat.restrictScalars C.toPolynomialRing.toRingHom

noncomputable def cutG : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.TangentAlgebra k))
noncomputable def cutT : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.xMultiply k).ker)
noncomputable def cutA : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.HeadAlgebra k))
noncomputable def cutN : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) ((S.nonAperyIdeal k).restrictScalars k))
noncomputable def cutQ : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.AperyAlgebra k))

/-- The chosen P variable acts by the same actual degree-one form in A. -/
theorem cutA_X_smul (i : Fin S.actualCutRank) (a : C.cutA) :
    (MvPolynomial.X i : S.CutPolynomialRing k) • a =
      (C.forms i).val * (show S.HeadAlgebra k from a) := by
  change S.polynomialToA k (C.toPolynomialRing (MvPolynomial.X i)) * (show S.HeadAlgebra k from a) = _
  rw [C.toPolynomialRing_X,C.polynomialForm_image]

/-- The actual same-jump S₀ isomorphism restricts through precisely this cut. -/
noncomputable def sameJumpCutIso (s : ℕ) (hs : 0 < s) :
    C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s)) ≅
      C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s)) :=
  C.restrictFunctor.mapIso (S.jumpStratumEquiv k s hs).toModuleIso

end LinearCutData

/-- Finite coefficient fields are handled on this fixed infinite extension;
Run13 supplies the actual Betti descent, in the same characteristic. -/
noncomputable def infiniteFieldCut (he : 3 ≤ S.embeddingDimension) :
    S.LinearCutData (NSP14.Homological.InfiniteScalarField k) :=
  S.fixedLinearCut (NSP14.Homological.InfiniteScalarField k) he

end NSP14.NumericalSemigroup
