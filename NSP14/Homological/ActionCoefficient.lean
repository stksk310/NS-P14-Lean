module
public import NSP14.Homological.ActionKoszul
public import NSP14.Homological.CoefficientKoszulListFunctor
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k R A : Type u) [Field k] [CommRing R] [CommRing A] [Algebra k R] [Algebra k A]

noncomputable def algebraRestrictionCoefficientEquiv (φ : R →ₐ[k] A) (M : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars (algebraMap k R)).obj ((ModuleCat.restrictScalars φ.toRingHom).obj M) ≃ₗ[k]
      (ModuleCat.restrictScalars (algebraMap k A)).obj M where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    change φ (algebraMap k R c) • (show M from a)=(algebraMap k A c) • (show M from a)
    rw [φ.commutes]

noncomputable def algebraRestrictionCoefficientComplexIso (φ : R →ₐ[k] A)
    (K : ChainComplex (ModuleCat.{u} A) ℕ) :
    ((ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((ModuleCat.restrictScalars φ.toRingHom).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ≅
        ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (algebraRestrictionCoefficientEquiv k R A φ (K.X i)).toModuleIso) (by intro i j _;rfl)

noncomputable def actionCoefficientComplex (rs : List A) (M : ModuleCat.{u} A) :
    ChainComplex (ModuleCat.{u} k) ℕ :=
  ((ModuleCat.restrictScalars (algebraMap k A)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    ((actionKoszulFunctor A rs).obj M)

variable (σ : Type u)
/-- The native complex with every commuting A-action retained computes
the actual polynomial-variable complex after coefficient restriction. -/
noncomputable def polynomialActionCoefficientIso (φ : VariableRing k σ →ₐ[k] A)
    (xs : List σ) (M : ModuleCat.{u} A) :
    actionCoefficientComplex k A (xs.map (fun x => φ (MvPolynomial.X x))) M ≅
      (coefficientKoszulListFunctor k σ xs).obj ((ModuleCat.restrictScalars φ.toRingHom).obj M) :=
  (algebraRestrictionCoefficientComplexIso k (VariableRing k σ) A φ _).symm ≪≫
    ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex _).mapIso
      (polynomialActionKoszulIso k σ φ.toRingHom xs M)
end NSP14.Homological
