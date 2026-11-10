module

public import NSP14.Homological.KoszulPolynomialBaseChange
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum

namespace NSP14.Homological

universe u
variable (k : Type u) [Field k]

/-- A family of actual complexes as a complex in the category of families. -/
noncomputable def familyComplex (C : ℤ → ChainComplex (ModuleCat.{u} k) ℕ) :
    ChainComplex (Discrete ℤ ⥤ ModuleCat.{u} k) ℕ where
  X i := Discrete.functor (fun t => (C t).X i)
  d i j := Discrete.natTrans (fun t => (C t.as).d i j)
  shape i j h := by apply NatTrans.ext; funext t; exact (C t.as).shape i j h
  d_comp_d' i j l _ _ := by apply NatTrans.ext; funext t; exact (C t.as).d_comp_d i j l

noncomputable def directSumComplex (C : ℤ → ChainComplex (ModuleCat.{u} k) ℕ) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ((colim : (Discrete ℤ ⥤ ModuleCat.{u} k) ⥤ ModuleCat.{u} k).mapHomologicalComplex _).obj (familyComplex k C)

/-- Arbitrary direct sums of vector spaces are exact, so this homology comparison
is valid even when the chain groups have infinite dimension. -/
noncomputable def directSumHomologyIso (C : ℤ → ChainComplex (ModuleCat.{u} k) ℕ) (i : ℕ) :
    (directSumComplex k C).homology i ≅ ModuleCat.of k (⨁ t : ℤ,(C t).homology i) := by
  let B := familyComplex k C
  let F : (Discrete ℤ ⥤ ModuleCat.{u} k) ⥤ ModuleCat.{u} k := colim
  let e : B.homology i ≅ Discrete.functor (fun t => (C t).homology i) :=
    Discrete.natIso (fun t => ((B.sc i).mapHomologyIso ((evaluation _ _).obj t)).symm)
  exact (B.sc i).mapHomologyIso F ≪≫ F.mapIso e ≪≫ ModuleCat.coprodIsoDirectSum _

end NSP14.Homological
