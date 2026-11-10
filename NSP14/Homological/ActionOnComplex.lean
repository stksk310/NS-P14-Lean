module
public import NSP14.Homological.ActionKoszul
public import NSP14.Homological.KoszulExactness
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R]

/-- The actual iterated cones on a complex, retaining native scalar actions. -/
noncomputable def actionOnComplex : List R →
    ChainComplex (ModuleCat.{u} R) ℕ ⥤ ChainComplex (ModuleCat.{u} R) ℕ
  | [] => 𝟭 _
  | r::rs => actionOnComplex rs ⋙ scalarConeFunctor R r

noncomputable instance actionOnComplex_additive (rs : List R) : (actionOnComplex R rs).Additive := by
  induction rs with
  | nil => change (𝟭 (ChainComplex (ModuleCat R) ℕ)).Additive;infer_instance
  | cons r rs ih =>
    let := ih
    change (actionOnComplex R rs ⋙ scalarConeFunctor R r).Additive
    infer_instance

noncomputable def actionOnComplex_singleIso (rs : List R) (M : ModuleCat.{u} R) :
    (actionOnComplex R rs).obj ((ChainComplex.single₀ _).obj M) ≅
      (actionKoszulFunctor R rs).obj M := by
  induction rs with
  | nil => exact Iso.refl _
  | cons r rs ih => exact (scalarConeFunctor R r).mapIso ih

theorem actionOnComplex_shortExact (rs : List R)
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact) :
    (S.map (actionOnComplex R rs)).ShortExact := by
  induction rs with
  | nil => simpa only [actionOnComplex,ShortComplex.map_id] using hS
  | cons r rs ih =>
    change (S.map (actionOnComplex R rs ⋙ scalarConeFunctor R r)).ShortExact
    rw [ShortComplex.map_comp]
    exact scalarCone_shortExact R r _ ih
end NSP14.Homological
