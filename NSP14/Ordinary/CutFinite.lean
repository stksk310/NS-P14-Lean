module
public import NSP14.Semigroup.FixedTower
public import NSP14.Homological.RestrictedScalars
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def cutCoefficientEquiv (M : Type) [AddCommGroup M] [Module k M]
    [Module (S.PolynomialRing k) M] [IsScalarTower k (S.PolynomialRing k) M] :
    NSP14.Homological.coefficientModule k (Fin S.actualCutRank)
      (C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) M)) ≃ₗ[k] M :=
  (NSP14.Homological.restrictedCoefficientEquiv C.toPolynomialRing _).trans
    (NSP14.Homological.originalCoefficientEquiv k S.NonXAtom M)

theorem cut_coefficientFinite (M : Type) [AddCommGroup M] [Module k M]
    [Module (S.PolynomialRing k) M] [IsScalarTower k (S.PolynomialRing k) M]
    [Module.Finite k M] : Module.Finite k
      (NSP14.Homological.coefficientModule k (Fin S.actualCutRank)
        (C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) M))) :=
  Module.Finite.equiv (C.cutCoefficientEquiv M).symm

/-- Finite coefficient spaces remain finite modules over the selected P. This
lemma does not apply to G, whose coefficient space is infinite. -/
theorem cut_finite (M : Type) [AddCommGroup M] [Module k M] [Module (S.PolynomialRing k) M]
    [IsScalarTower k (S.PolynomialRing k) M] [Module.Finite k M] :
    Module.Finite (S.CutPolynomialRing k)
      (C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) M)) := by
  have : Module.Finite k (NSP14.Homological.coefficientModule k S.NonXAtom
      (ModuleCat.of (S.PolynomialRing k) M)) :=
    Module.Finite.equiv (NSP14.Homological.originalCoefficientEquiv k S.NonXAtom M).symm
  exact NSP14.Homological.restrictPolynomial_finite C.toPolynomialRing _

theorem cutA_finite : Module.Finite (S.CutPolynomialRing k) C.cutA := C.cut_finite (S.HeadAlgebra k)
theorem cutT_finite : Module.Finite (S.CutPolynomialRing k) C.cutT := C.cut_finite (S.xMultiply k).ker
theorem cutN_finite : Module.Finite (S.CutPolynomialRing k) C.cutN := C.cut_finite ((S.nonAperyIdeal k).restrictScalars k)
theorem cutQ_finite : Module.Finite (S.CutPolynomialRing k) C.cutQ := C.cut_finite (S.AperyAlgebra k)
theorem cutStage_finite (s : ℕ) : Module.Finite (S.CutPolynomialRing k) (C.cutStage s) :=
  C.cut_finite (S.TowerStage k s)
theorem cutHigh_finite (s n : ℕ) : Module.Finite (S.CutPolynomialRing k) (C.cutHigh s n) := by
  let f : ↥(S.towerHighIdeal k s n) →ₗ[k] S.TowerStage k s :=
    { toFun a := a.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : Module.Finite k ↥(S.towerHighIdeal k s n) := Module.Finite.of_injective f Subtype.val_injective
  exact C.cut_finite ↥(S.towerHighIdeal k s n)
theorem cutK_finite (s : ℕ) : Module.Finite (S.CutPolynomialRing k) (C.cutK s) := by
  let f : S.TowerK k s →ₗ[k] S.TowerStage k s :=
    { toFun a := a.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : Module.Finite k (S.TowerK k s) := Module.Finite.of_injective f Subtype.val_injective
  exact C.cut_finite (S.TowerK k s)

theorem cutA_coefficientFinite : Module.Finite k
    (NSP14.Homological.coefficientModule k (Fin S.actualCutRank) C.cutA) :=
  C.cut_coefficientFinite (S.HeadAlgebra k)
theorem cutT_coefficientFinite : Module.Finite k
    (NSP14.Homological.coefficientModule k (Fin S.actualCutRank) C.cutT) :=
  C.cut_coefficientFinite (S.xMultiply k).ker
theorem cutHigh_coefficientFinite (s n : ℕ) : Module.Finite k
    (NSP14.Homological.coefficientModule k (Fin S.actualCutRank) (C.cutHigh s n)) := by
  let f : ↥(S.towerHighIdeal k s n) →ₗ[k] S.TowerStage k s :=
    { toFun a := a.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : Module.Finite k ↥(S.towerHighIdeal k s n) := Module.Finite.of_injective f Subtype.val_injective
  exact C.cut_coefficientFinite ↥(S.towerHighIdeal k s n)
theorem cutK_coefficientFinite (s : ℕ) : Module.Finite k
    (NSP14.Homological.coefficientModule k (Fin S.actualCutRank) (C.cutK s)) := by
  let f : S.TowerK k s →ₗ[k] S.TowerStage k s :=
    { toFun a := a.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have : Module.Finite k (S.TowerK k s) := Module.Finite.of_injective f Subtype.val_injective
  exact C.cut_coefficientFinite (S.TowerK k s)
end NSP14.NumericalSemigroup.LinearCutData
