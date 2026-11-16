module
public import NSP14.Ordinary.CutFinite
public import NSP14.Homological.FiniteKoszulEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def cutTowerSequence (s : ℕ) (hs : 1 ≤ s) :
    ShortComplex (ModuleCat (S.CutPolynomialRing k)) :=
  ShortComplex.mk (C.cutKInclusion s hs) (C.cutTowerStep s) (by
    ext a
    exact ((C.cutTower_exact s hs).2.1 _).2 ⟨a,rfl⟩)

theorem cutTowerSequence_shortExact (s : ℕ) (hs : 1 ≤ s) :
    (C.cutTowerSequence s hs).ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (C.cutTower_exact s hs).2.1
  mono_f := (ModuleCat.mono_iff_injective _).mpr (C.cutTower_exact s hs).1
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (C.cutTower_exact s hs).2.2

noncomputable def cutHighEuler (s n j : ℕ) : ℤ := by
  let := C.cutHigh_finite s n
  exact NSP14.Homological.bettiEuler k (Fin S.actualCutRank) (C.cutHigh s n) j

noncomputable def cutKEuler (s j : ℕ) : ℤ := by
  let := C.cutK_finite s
  exact NSP14.Homological.bettiEuler k (Fin S.actualCutRank) (C.cutK s) j

/-- The third Tor inequality, now applied to the actual Run14 tower with
its one fixed P action. No connecting map is assumed zero. -/
theorem cutTower_kernel_le (s : ℕ) (hs : 1 ≤ s) (j : ℕ) :
    C.cutKEuler s j ≤ C.cutHighEuler s (s+1) j+C.cutHighEuler (s+1) (s+1) (j+1) := by
  let := C.cutK_finite s
  let := C.cutHigh_finite s (s+1)
  let := C.cutHigh_finite (s+1) (s+1)
  let : Module.Finite (S.CutPolynomialRing k) (C.cutTowerSequence s hs).X₁ := C.cutK_finite s
  let : Module.Finite (S.CutPolynomialRing k) (C.cutTowerSequence s hs).X₂ := C.cutHigh_finite s (s+1)
  let : Module.Finite (S.CutPolynomialRing k) (C.cutTowerSequence s hs).X₃ := C.cutHigh_finite (s+1) (s+1)
  exact NSP14.Homological.bettiEuler_kernel_le k (Fin S.actualCutRank)
    (C.cutTowerSequence s hs) (C.cutTowerSequence_shortExact s hs) j

/-- The actual same-jump quotient, followed by the tower-kernel map.
Its grading shift remains the separately proved +s of sameJumpCutIso_degree. -/
noncomputable def descendingToTowerKIso (s : ℕ) (hs : 0 < s) :
    C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s)) ≅ C.cutK s :=
  C.sameJumpCutIso s hs ≪≫ C.towerStratumCutIso s

theorem descendingStratumCut_finite (s : ℕ) (hs : 0 < s) :
    Module.Finite (S.CutPolynomialRing k)
      (C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s))) := by
  let := C.cutK_finite s
  exact Module.Finite.equiv (C.descendingToTowerKIso s hs).symm.toLinearEquiv

noncomputable def descendingStratumEuler (s : ℕ) (hs : 0 < s) (j : ℕ) : ℤ := by
  let := C.descendingStratumCut_finite s hs
  exact NSP14.Homological.bettiEuler k (Fin S.actualCutRank)
    (C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s))) j

/-- Transport only the same-jump strata to Tor, never the global T/N vector
space equivalence. -/
theorem descendingStratumEuler_eq (s : ℕ) (hs : 0 < s) (j : ℕ) :
    C.descendingStratumEuler s hs j=C.cutKEuler s j := by
  let := C.cutK_finite s
  let := C.descendingStratumCut_finite s hs
  have hb := NSP14.Homological.totalBetti_iso k (Fin S.actualCutRank)
    (C.descendingToTowerKIso s hs)
  unfold descendingStratumEuler cutKEuler NSP14.Homological.bettiEuler
  exact congrArg (fun b : ℕ → ℕ => NSP14.Homological.partialEuler b j) (funext hb)

theorem cutHighEuler_top (s n : ℕ) : C.cutHighEuler s n S.actualCutRank=0 := by
  let := C.cutHigh_finite s n
  let := C.cutHigh_coefficientFinite s n
  change NSP14.Homological.bettiEuler k (Fin S.actualCutRank) (C.cutHigh s n) S.actualCutRank=0
  simpa only [Fintype.card_fin] using NSP14.Homological.finite_koszul_bettiEuler_top k (Fin S.actualCutRank) (C.cutHigh s n)
    (by simp only [Fintype.card_fin];have := S.actualCutRank_two_le;omega)

theorem cutKEuler_top (s : ℕ) : C.cutKEuler s S.actualCutRank=0 := by
  let := C.cutK_finite s
  let := C.cutK_coefficientFinite s
  change NSP14.Homological.bettiEuler k (Fin S.actualCutRank) (C.cutK s) S.actualCutRank=0
  simpa only [Fintype.card_fin] using NSP14.Homological.finite_koszul_bettiEuler_top k (Fin S.actualCutRank) (C.cutK s)
    (by simp only [Fintype.card_fin];have := S.actualCutRank_two_le;omega)
end NSP14.NumericalSemigroup.LinearCutData
