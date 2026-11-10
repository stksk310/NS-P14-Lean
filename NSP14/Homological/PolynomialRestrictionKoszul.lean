module
public import NSP14.Homological.RestrictedScalars
public import NSP14.Homological.KoszulTor
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k τ σ : Type u) [Field k]
  (φ : VariableRing k τ →ₐ[k] VariableRing k σ) (v : τ → σ)
  (hφ : ∀ t,φ (MvPolynomial.X t)=MvPolynomial.X (v t))

include hφ in
theorem restrict_variable_chain (t : τ) (K : ChainComplex (ModuleCat.{u} (VariableRing k σ)) ℕ) :
    ((ModuleCat.restrictScalars φ.toRingHom).mapHomologicalComplex (ComplexShape.down ℕ)).map
      ((MvPolynomial.X (v t) : VariableRing k σ) • 𝟙 K)=
        (MvPolynomial.X t : VariableRing k τ) •
          𝟙 (((ModuleCat.restrictScalars φ.toRingHom).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  ext a
  change (MvPolynomial.X (v t) : VariableRing k σ) • (show K.X i from a)=
    φ (MvPolynomial.X t) • (show K.X i from a)
  rw [hφ]

/-- Restriction of the actual variable action commutes with the concrete
Koszul recursion. Injectivity of the polynomial map is not assumed. -/
noncomputable def polynomialRestrictionKoszulIso (xs : List τ) (M : ModuleCat.{u} (VariableRing k σ)) :
    ((ModuleCat.restrictScalars φ.toRingHom).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (koszulList k σ (xs.map v) M) ≅
        koszulList k τ xs ((ModuleCat.restrictScalars φ.toRingHom).obj M) := by
  induction xs with
  | nil => exact (singleMapHomologicalComplex (ModuleCat.restrictScalars φ.toRingHom) (ComplexShape.down ℕ) 0).app M
  | cons t xs ih =>
    let K := koszulList k σ (xs.map v) M
    exact homotopyCofiber.mapHomologicalComplexObjIso
        ((MvPolynomial.X (v t) : VariableRing k σ) • 𝟙 K) (ModuleCat.restrictScalars φ.toRingHom) ≪≫
      eqToIso (by rw [restrict_variable_chain k τ σ φ v hφ t K];rfl) ≪≫
      (scalarConeFunctor (VariableRing k τ) (MvPolynomial.X t)).mapIso ih

/-- Coefficient actions agree through the k-algebra map, with literal
identity component maps on an arbitrary (possibly infinite) complex. -/
noncomputable def restrictedCoefficientComplexIso
    (K : ChainComplex (ModuleCat.{u} (VariableRing k σ)) ℕ) :
    ((ModuleCat.restrictScalars (algebraMap k (VariableRing k τ))).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (((ModuleCat.restrictScalars φ.toRingHom).mapHomologicalComplex (ComplexShape.down ℕ)).obj K) ≅
        ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomologicalComplex (ComplexShape.down ℕ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (restrictedCoefficientEquiv φ (K.X i)).toModuleIso)
    (by intro i j _;rfl)
end NSP14.Homological
