module
public import NSP14.Ordinary.TowerEuler
public import NSP14.Semigroup.CutGeneratorCount
public import NSP14.Homological.KoszulVariableSpace
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

theorem cutHigh_variables (s n : ℕ) :
    koszulVariableSubmodule k (Fin S.actualCutRank) (variableList k (Fin S.actualCutRank))
      (C.cutHigh s n)=C.positiveSpace s n := by
  rw [koszulVariableSubmodule_all]
  apply iSup_congr
  intro i
  congr 1

/-- The actual zeroth homology, including its induced coefficient action,
is the actual bottom degree. This is needed at j=1 in the tower estimate. -/
noncomputable def cutHighH0Equiv (s n : ℕ) (hn : 1 ≤ n) :
    koszulHomologyK k (Fin S.actualCutRank) (C.cutHigh s n) 0 ≃ₗ[k]
      S.towerStageDegree k s n := by
  let eP := (koszulH0Equiv k (Fin S.actualCutRank) (variableList k (Fin S.actualCutRank))
      (C.cutHigh s n)).trans (Submodule.quotEquivOfEq _ _ (C.cutHigh_variables s n))
  let eK := ((ModuleCat.restrictScalars (algebraMap k (S.CutPolynomialRing k))).mapIso eP.toModuleIso).toLinearEquiv
  let eQ := originalCoefficientEquiv k (Fin S.actualCutRank) (C.cutHigh s n ⧸ C.positiveSpace s n)
  exact eK.trans (eQ.trans ((Submodule.Quotient.restrictScalarsEquiv k (C.positiveSpace s n)).symm.trans
    (C.cutGeneratorQuotientEquiv s n hn)))

theorem cutHighEuler_zero (s n : ℕ) (hn : 1 ≤ n) :
    C.cutHighEuler s n 0=Module.finrank k (S.towerStageDegree k s n) := by
  let := C.cutHigh_finite s n
  change bettiEuler k (Fin S.actualCutRank) (C.cutHigh s n) 0=_
  rw [bettiEuler_zero]
  exact_mod_cast (C.cutHighH0Equiv s n hn).finrank_eq
end NSP14.NumericalSemigroup.LinearCutData
