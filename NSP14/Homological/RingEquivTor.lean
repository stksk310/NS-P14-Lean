module
public import NSP14.Homological.RingEquivTensor
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
namespace NSP14.Homological
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S)

/-- Restriction by a ring equivalence preserves ordinary derived Tor.
This compares actual projective resolutions and tensor functors. -/
noncomputable def ringEquivTorIso (M N : ModuleCat.{u} S) (i : ℕ) :
    (((CategoryTheory.Tor (ModuleCat R) i).obj ((ModuleCat.restrictScalars e.toRingHom).obj M)).obj
      ((ModuleCat.restrictScalars e.toRingHom).obj N)) ≅
    (ModuleCat.restrictScalars e.toRingHom).obj (((CategoryTheory.Tor (ModuleCat S) i).obj M).obj N) := by
  let F := ModuleCat.restrictScalars e.toRingHom
  let P := projectiveResolution N
  let Q := F.mapProjectiveResolution P
  let T := (tensoringLeft (ModuleCat S)).obj M
  let U := (tensoringLeft (ModuleCat R)).obj (F.obj M)
  let a := Q.isoLeftDerivedObj U i
  let b := (homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) i).mapIso
    ((NatIso.mapHomologicalComplex (restrictTensorNatIso e M) (ComplexShape.down ℕ)).app P.complex)
  let c := (((T.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex).sc i).mapHomologyIso F
  let d := F.mapIso (P.isoLeftDerivedObj T i).symm
  exact a ≪≫ b ≪≫ c ≪≫ d
end NSP14.Homological
