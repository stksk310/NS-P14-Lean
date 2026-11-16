module
public import NSP14.Semigroup.TowerExact
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable def ascendingToTowerK (s : ℕ) :
    S.ascendingJump k s →ₗ[S.PolynomialRing k] S.TowerK k s where
  toFun a := ⟨Ideal.Quotient.mk _ a.val.val,Ideal.mem_map_of_mem _ a.property⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r a := by
    apply Subtype.ext
    exact (Ideal.Quotient.mkₐ (S.PolynomialRing k) (S.jumpIdeal k (s-1))).toLinearMap.map_smul r a.val.val

theorem ascendingToTowerK_ker (s : ℕ) :
    (S.ascendingToTowerK k s).ker = S.previousAscendingJump k s := by
  ext a
  rw [LinearMap.mem_ker,Subtype.ext_iff]
  change Ideal.Quotient.mk (S.jumpIdeal k (s-1)) a.val.val=0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  rfl

theorem ascendingToTowerK_surjective (s : ℕ) : Function.Surjective (S.ascendingToTowerK k s) := by
  intro a
  obtain ⟨b,hb,he⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 a.property
  exact ⟨⟨⟨b,S.jumpIdeal_le_nonAperyIdeal k s hb⟩,hb⟩,Subtype.ext he⟩

/-- The kernel term in the actual tower is exactly Run12's actual same-jump
ascending quotient, as an S₀ module, not only as a vector space. -/
noncomputable def towerStratumEquiv (s : ℕ) :
    S.AscendingJumpStratum k s ≃ₗ[S.PolynomialRing k] S.TowerK k s :=
  (Submodule.quotEquivOfEq _ _ (S.ascendingToTowerK_ker k s).symm).trans
    ((S.ascendingToTowerK k s).quotKerEquivOfSurjective (S.ascendingToTowerK_surjective k s))

namespace LinearCutData
variable {S k} (C : S.LinearCutData k)
noncomputable def cutK (s : ℕ) : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.TowerK k s))
noncomputable def towerStratumCutIso (s : ℕ) :
    C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s)) ≅ C.cutK s :=
  C.restrictFunctor.mapIso (S.towerStratumEquiv k s).toModuleIso
end LinearCutData
end NSP14.NumericalSemigroup
