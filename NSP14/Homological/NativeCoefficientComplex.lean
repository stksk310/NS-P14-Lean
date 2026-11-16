module
public import NSP14.Homological.H0KernelHomology
public import NSP14.Homological.EndomorphismConeBound
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]

noncomputable def nativeCoefficientFunctor :
    ChainComplex (ModuleCat.{u} R) ℕ ⥤ ChainComplex (ModuleCat.{u} k) ℕ :=
  (ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex (ComplexShape.down ℕ)

noncomputable instance nativeCoefficientFunctor_additive : (nativeCoefficientFunctor k R).Additive := by
  unfold nativeCoefficientFunctor
  infer_instance

theorem nativeCoefficient_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact) :
    (S.map (nativeCoefficientFunctor k R)).ShortExact := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  unfold nativeCoefficientFunctor
  exact hS.map _

noncomputable def nativeCoefficientComplex (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ChainComplex (ModuleCat.{u} k) ℕ := (nativeCoefficientFunctor k R).obj K

noncomputable def nativeCoefficientHomologyIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (nativeCoefficientComplex k R K).homology i ≅
      (ModuleCat.restrictScalars (algebraMap k R)).obj (K.homology i) :=
  (K.sc i).mapHomologyIso (ModuleCat.restrictScalars (algebraMap k R))

noncomputable def coefficientH0KernelPositiveIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (i : ℕ) :
    (nativeCoefficientComplex k R (h0KernelSequence R K).X₁).homology (i+1) ≅
      (nativeCoefficientComplex k R K).homology (i+1) :=
  nativeCoefficientHomologyIso k R _ (i+1) ≪≫
    (ModuleCat.restrictScalars (algebraMap k R)).mapIso (h0KernelHomologyPositiveIso R K i) ≪≫
      (nativeCoefficientHomologyIso k R K (i+1)).symm

theorem coefficientH0KernelZero (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    IsZero ((nativeCoefficientComplex k R (h0KernelSequence R K).X₁).homology 0) :=
  IsZero.of_iso ((ModuleCat.restrictScalars (algebraMap k R)).map_isZero (h0KernelHomologyZero R K))
    (nativeCoefficientHomologyIso k R _ 0)

noncomputable def nativeCoefficientConeIso (K : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    nativeCoefficientComplex k R ((scalarConeFunctor R r).obj K) ≅
      homotopyCofiber ((nativeCoefficientFunctor k R).map (r • 𝟙 K)) :=
  homotopyCofiber.mapHomologicalComplexObjIso _ (ModuleCat.restrictScalars (algebraMap k R))

variable (K : ChainComplex (ModuleCat.{u} R) ℕ)
  [∀ i,Module.Finite k ((nativeCoefficientComplex k R K).homology i)]

theorem coefficientH0Kernel_finite (i : ℕ) :
    Module.Finite k ((nativeCoefficientComplex k R (h0KernelSequence R K).X₁).homology i) := by
  cases i with
  | zero =>
    have : Subsingleton ((nativeCoefficientComplex k R (h0KernelSequence R K).X₁).homology 0) :=
      ModuleCat.subsingleton_of_isZero (coefficientH0KernelZero k R K)
    infer_instance
  | succ i => exact Module.Finite.equiv (coefficientH0KernelPositiveIso k R K i).symm.toLinearEquiv

theorem nativeCoefficientCone_finite (r : R) (i : ℕ) :
    Module.Finite k ((nativeCoefficientComplex k R ((scalarConeFunctor R r).obj K)).homology i) := by
  let : Module.Finite k ((homotopyCofiber ((nativeCoefficientFunctor k R).map (r • 𝟙 K))).homology i) :=
    endomorphismCone_homology_finite k (nativeCoefficientComplex k R K) _ i
  let e : (nativeCoefficientComplex k R ((scalarConeFunctor R r).obj K)).homology i ≅
      (homotopyCofiber ((nativeCoefficientFunctor k R).map (r • 𝟙 K))).homology i :=
    (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (nativeCoefficientConeIso k R K r)
  exact Module.Finite.equiv e.symm.toLinearEquiv

theorem nativeCoefficientCone_bound (r : R) (i : ℕ) :
    Module.finrank k ((nativeCoefficientComplex k R ((scalarConeFunctor R r).obj K)).homology i) ≤
      Module.finrank k ((nativeCoefficientComplex k R K).homology i)+
        (if i=0 then 0 else Module.finrank k ((nativeCoefficientComplex k R K).homology (i-1))) := by
  let e : (nativeCoefficientComplex k R ((scalarConeFunctor R r).obj K)).homology i ≅
      (homotopyCofiber ((nativeCoefficientFunctor k R).map (r • 𝟙 K))).homology i :=
    (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (nativeCoefficientConeIso k R K r)
  rw [e.toLinearEquiv.finrank_eq]
  exact endomorphismCone_finrank_le k (nativeCoefficientComplex k R K) _ i
end NSP14.Homological
