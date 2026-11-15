module
public import NSP14.Homological.IdealAdjoining
public import NSP14.Homological.RegularModuleReduction
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R] (J : Ideal R) (g : R)

theorem idealScalar_range :
    (g • 𝟙 (ModuleCat.of R (R ⧸ J))).hom.range=(idealAdjoinLeft R J g).hom.range := by
  ext a
  constructor
  · rintro ⟨b,rfl⟩
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective J b
    exact ⟨Submodule.Quotient.mk x,rfl⟩
  · rintro ⟨b,rfl⟩
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (J.colon {g}) b
    exact ⟨Submodule.Quotient.mk x,rfl⟩

theorem idealScalar_range_ker :
    (g • 𝟙 (ModuleCat.of R (R ⧸ J))).hom.range=(idealAdjoinRight R J g).hom.ker := by
  have h := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp
    (idealAdjoinSequence_shortExact R J g).exact
  exact (idealScalar_range R J g).trans h

/-- Quotienting the actual R/J by multiplication by g is the actual
R/(J+(g)); no regularity or finiteness is assumed. -/
noncomputable def idealScalarQuotientIso :
    scalarModuleQuotient R g (ModuleCat.of R (R ⧸ J)) ≅
      ModuleCat.of R (R ⧸ (J ⊔ Ideal.span {g})) := by
  let f := (idealAdjoinRight R J g).hom
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (J ⊔ Ideal.span {g}) a
    exact ⟨Submodule.Quotient.mk x,rfl⟩
  exact ((Submodule.quotEquivOfEq _ _ (idealScalar_range_ker R J g)).trans
    (LinearMap.quotKerEquivOfSurjective f hf)).toModuleIso

theorem idealScalarQuotientIso_mk (x : R) :
    (idealScalarQuotientIso R J g).hom
      (Submodule.Quotient.mk (Submodule.Quotient.mk x : R ⧸ J))=
        (Submodule.Quotient.mk x : R ⧸ (J ⊔ Ideal.span {g})) := by
  rfl

end NSP14.Homological
