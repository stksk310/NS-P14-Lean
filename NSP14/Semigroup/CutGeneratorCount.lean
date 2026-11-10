module
public import NSP14.Semigroup.FixedTower
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable instance cutHighKModule (s n : ℕ) : Module k (C.cutHigh s n) :=
  Module.compHom (C.cutHigh s n) (algebraMap k (S.CutPolynomialRing k))
noncomputable instance cutHighKTower (s n : ℕ) : IsScalarTower k (S.CutPolynomialRing k) (C.cutHigh s n) :=
  IsScalarTower.of_compHom k (S.CutPolynomialRing k) (C.cutHigh s n)

/-- The k structure induced through P is the actual coefficient structure. -/
noncomputable def cutHighKEquiv (s n : ℕ) :
    C.cutHigh s n ≃ₗ[k] ↥(S.towerHighIdeal k s n) where
  toFun a := ⟨a.val,a.property⟩
  invFun a := ⟨a.val,a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r a := by
    apply Subtype.ext
    change S.polynomialToA k (C.toPolynomialRing (algebraMap k (S.CutPolynomialRing k) r)) • a.val = r • a.val
    rw [C.toPolynomialRing.commutes,(S.polynomialToA k).commutes,algebraMap_smul]

noncomputable def cutBottomProjection (s n : ℕ) :
    C.cutHigh s n →ₗ[k] (S.StageDegreeExponent s n →₀ k) :=
  (S.truncBottomProjection k s n).comp (C.cutHighKEquiv s n).toLinearMap

theorem cutBottomProjection_ker (s n : ℕ) (hn : 1 ≤ n) :
    (C.cutBottomProjection s n).ker = (C.positiveSpace s n).restrictScalars k := by
  ext a
  change S.truncBottomProjection k s n (C.cutHighKEquiv s n a)=0 ↔ a ∈ C.positiveSpace s n
  rw [← LinearMap.mem_ker,S.truncBottomProjection_ker]
  exact (C.positiveSpace_mem_iff s n hn a).symm

theorem cutBottomProjection_surjective (s n : ℕ) : Function.Surjective (C.cutBottomProjection s n) :=
  (S.truncBottomProjection_surjective k s n).comp (C.cutHighKEquiv s n).surjective

/-- Actual augmentation quotient ≃ actual bottom degree. This proves the
minimal generator count, rather than merely exhibiting a spanning family. -/
noncomputable def cutGeneratorQuotientEquiv (s n : ℕ) (hn : 1 ≤ n) :
    (C.cutHigh s n ⧸ (C.positiveSpace s n).restrictScalars k) ≃ₗ[k] S.towerStageDegree k s n :=
  ((Submodule.quotEquivOfEq _ _ (C.cutBottomProjection_ker s n hn).symm).trans
    ((C.cutBottomProjection s n).quotKerEquivOfSurjective (C.cutBottomProjection_surjective s n))).trans
      (S.stageDegreeCoordinates k s n).symm

theorem cut_minimal_generator_count (s n : ℕ) (hn : 1 ≤ n) :
    Module.finrank k (C.cutHigh s n ⧸ (C.positiveSpace s n).restrictScalars k) =
      Module.finrank k (S.towerStageDegree k s n) := (C.cutGeneratorQuotientEquiv s n hn).finrank_eq
end NSP14.NumericalSemigroup.LinearCutData
