module
public import NSP14.Homological.IdealScalarQuotient
@[expose] public section
namespace NSP14.Tests.IdealScalarQuotient
noncomputable def actual_quotient_iso (R : Type) [CommRing R] (J : Ideal R) (g : R) :
    Homological.scalarModuleQuotient R g (ModuleCat.of R (R ⧸ J)) ≅
      ModuleCat.of R (R ⧸ (J ⊔ Ideal.span {g})) :=
  Homological.idealScalarQuotientIso R J g
end NSP14.Tests.IdealScalarQuotient
