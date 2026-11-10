module
public import NSP14.Semigroup.CutAugmentation
public import NSP14.Semigroup.TowerStratum
public import NSP14.Semigroup.JumpDegrees
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def cutKInclusion (s : ℕ) (hs : 1 ≤ s) :
    C.cutK s ⟶ C.cutHigh s (s+1) :=
  C.restrictFunctor.map (ModuleCat.ofHom (S.towerKInclusion k s hs))
noncomputable def cutTowerStep (s : ℕ) : C.cutHigh s (s+1) ⟶ C.cutHigh (s+1) (s+1) :=
  C.restrictFunctor.map (ModuleCat.ofHom (S.towerTruncStep k s (s+1)))

/-- All three maps use this exact P action. -/
theorem cutTower_exact (s : ℕ) (hs : 1 ≤ s) :
    Function.Injective (C.cutKInclusion s hs).hom ∧
    Function.Exact (C.cutKInclusion s hs).hom (C.cutTowerStep s).hom ∧
    Function.Surjective (C.cutTowerStep s).hom := S.tower_exact k s hs

/-- The positive-variable submodule has precisely the actual higher-degree
members. Together with truncGeneratorQuotientEquiv this identifies the
augmentation quotient with the actual bottom degree. -/
theorem positiveSpace_mem_iff (s n : ℕ) (hn : 1 ≤ n) (a : C.cutHigh s n) :
    a ∈ C.positiveSpace s n ↔ a.val ∈ S.towerHighIdeal k s (n+1) := by
  rw [C.positiveSpace_eq_next s n hn]
  constructor
  · rintro ⟨b,rfl⟩
    exact b.property
  · intro ha
    exact ⟨⟨a.val,ha⟩,Subtype.ext rfl⟩

/-- X_s and M_s are generated in degrees s and s+1 over the same P. -/
theorem cutTower_generated (s : ℕ) (hs : 1 ≤ s) :
    C.generatorSpace s s=⊤ ∧ C.generatorSpace s (s+1)=⊤ :=
  ⟨C.cutHigh_generated s s hs,C.cutHigh_generated s (s+1) (by omega)⟩

/-- Restriction of scalars preserves the inherited degree difference s. -/
theorem sameJumpCutIso_degree (s : ℕ) (hs : 0<s) (p : ℕ)
    (a : C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s))) :
    (C.sameJumpCutIso s hs).hom.hom a ∈ S.ascendingStratumDegree k s (p+s) ↔
      a ∈ S.descendingStratumDegree k s p := S.jumpStratumEquiv_degree k s hs p a

end NSP14.NumericalSemigroup.LinearCutData
