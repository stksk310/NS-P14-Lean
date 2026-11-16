module
public import NSP14.Homological.ActionKoszul
public import NSP14.Homological.ActionOnComplex
public import NSP14.Homological.KoszulLinearity
public import NSP14.Homological.ActionCoefficient
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R]

noncomputable instance actionKoszulFunctor_additive (rs : List R) : (actionKoszulFunctor R rs).Additive := by
  induction rs with
  | nil => change (ChainComplex.single₀ (ModuleCat R)).Additive;infer_instance
  | cons r rs ih =>
    let := ih
    change (actionKoszulFunctor R rs ⋙ scalarConeFunctor R r).Additive
    infer_instance

noncomputable instance actionKoszulFunctor_linear (rs : List R) : (actionKoszulFunctor R rs).Linear R := by
  induction rs with
  | nil => change (ChainComplex.single₀ (ModuleCat R)).Linear R;infer_instance
  | cons r rs ih =>
    let := ih
    change (actionKoszulFunctor R rs ⋙ scalarConeFunctor R r).Linear R
    infer_instance

theorem actionKoszulFunctor_shortExact (rs : List R) (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (actionKoszulFunctor R rs)).ShortExact := by
  induction rs with
  | nil =>
    change (S.map (ChainComplex.single₀ (ModuleCat R))).ShortExact
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    exact hS.map _
  | cons r rs ih =>
    change (S.map (actionKoszulFunctor R rs ⋙ scalarConeFunctor R r)).ShortExact
    rw [ShortComplex.map_comp]
    exact scalarCone_shortExact R r _ ih

variable (k : Type u) [Field k] [Algebra k R]
noncomputable def actionCoefficientFunctor (rs : List R) :
    ModuleCat.{u} R ⥤ ChainComplex (ModuleCat.{u} k) ℕ :=
  actionKoszulFunctor R rs ⋙
    (ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex (ComplexShape.down ℕ)

noncomputable instance actionCoefficientFunctor_additive (rs : List R) : (actionCoefficientFunctor R k rs).Additive := by
  unfold actionCoefficientFunctor
  infer_instance

theorem actionCoefficientFunctor_shortExact (rs : List R) (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (actionCoefficientFunctor R k rs)).ShortExact := by
  unfold actionCoefficientFunctor
  rw [ShortComplex.map_comp]
  have hK := actionKoszulFunctor_shortExact R rs S hS
  let : Mono (S.map (actionKoszulFunctor R rs)).f := hK.mono_f
  let : Epi (S.map (actionKoszulFunctor R rs)).g := hK.epi_g
  exact hK.map _

noncomputable def actionCoefficientConsIso (r : R) (rs : List R) (M : ModuleCat.{u} R) :
    actionCoefficientComplex k R (r::rs) M ≅ homotopyCofiber ((actionCoefficientFunctor R k rs).map (r • 𝟙 M)) := by
  let F := (ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex (ComplexShape.down ℕ)
  have he : (actionCoefficientFunctor R k rs).map (r • 𝟙 M)=
      F.map (r • 𝟙 ((actionKoszulFunctor R rs).obj M)) := by
    change F.map ((actionKoszulFunctor R rs).map (r • 𝟙 M))=_
    rw [CategoryTheory.Functor.map_smul,(actionKoszulFunctor R rs).map_id M]
  exact homotopyCofiber.mapHomologicalComplexObjIso _ (ModuleCat.restrictScalars (algebraMap k R)) ≪≫
    eqToIso (congrArg (fun f : F.obj ((actionKoszulFunctor R rs).obj M) ⟶ F.obj ((actionKoszulFunctor R rs).obj M) => homotopyCofiber f) he.symm)
end NSP14.Homological
