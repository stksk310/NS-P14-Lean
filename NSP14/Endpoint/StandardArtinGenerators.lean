module
public import NSP14.Endpoint.StandardArtinRows
public import NSP14.Homological.PrincipalBetti
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory CategoryTheory.Limits NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k σ : Type) [Field k] [Fintype σ] [LinearOrder σ]
  (I : Ideal (MvPolynomial σ k))

noncomputable def artinIdealModule : ModuleCat (VariableRing k σ) := ModuleCat.of _ I
noncomputable def artinIdealInclusion : artinIdealModule k σ I ⟶ ModuleCat.of (VariableRing k σ) (VariableRing k σ) :=
  ModuleCat.ofHom I.subtype
noncomputable def artinIdealProjection : ModuleCat.of (VariableRing k σ) (VariableRing k σ) ⟶ artinModule k σ I :=
  ModuleCat.ofHom (Y:=artinModule k σ I) I.mkQ
noncomputable def artinIdealSequence : ShortComplex (ModuleCat (VariableRing k σ)) :=
  ShortComplex.mk (artinIdealInclusion k σ I) (artinIdealProjection k σ I) (by
    apply ModuleCat.hom_ext
    ext a
    exact Submodule.Quotient.mk_eq_zero _ |>.mpr a.property)

omit [Fintype σ] [LinearOrder σ] in
theorem artinIdeal_shortExact : (artinIdealSequence k σ I).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range I.subtype=LinearMap.ker I.mkQ
    rw [Submodule.range_subtype,Submodule.ker_mkQ]
  · exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  · exact (ModuleCat.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _)

variable (hproper : I≠⊤) (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
omit [LinearOrder σ] in
include hproper hI in
theorem artinIdeal_h0_zero : (koszulHomologyFunctor k σ (variableList k σ) 0).map
    (artinIdealInclusion k σ I)=0 := by
  apply koszul_h0_map_zero_of_minimal
  intro a
  rw [polynomial_variable_submodule,variablesIdeal_all_eq_ker]
  change augmentation k σ a.val=0
  rw [show augmentation k σ a.val=a.val.coeff 0 from MvPolynomial.aeval_zero' _]
  exact homogeneous_ideal_constant k σ I hproper hI a.val a.property

/-- The genuine connecting map in 0→I→T→T/I→0 is the first Tor
isomorphism; no dimension input or minimality witness is assumed. -/
noncomputable def artinFirstIdealIso :
    koszulHomology k σ (variableList k σ) (artinModule k σ I) 1 ≅
      koszulHomology k σ (variableList k σ) (artinIdealModule k σ I) 0 := by
  let hS := koszul_shortExact k σ (variableList k σ) (artinIdealSequence k σ I) (artinIdeal_shortExact k σ I)
  let δ := hS.δ 1 0 rfl
  let : Mono δ := hS.mono_δ _ _ rfl (freeKoszulHomology_positive k σ
    (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) 0)
  let : Epi δ := (hS.homology_exact₁ 1 0 rfl).epi_f_iff.mpr (artinIdeal_h0_zero k σ I hproper hI)
  let := isIso_of_mono_of_epi δ
  exact asIso δ

instance artinIdealFinite : Module.Finite (VariableRing k σ) (artinIdealModule k σ I) := inferInstanceAs (Module.Finite _ I)

/-- Minimal generator number via the actual Nakayama fibre I/(y)I,
computed by its actual H0/Tor0. -/
noncomputable def idealGeneratorNumber : ℕ := totalBetti k σ (artinIdealModule k σ I) 0

omit [LinearOrder σ] in
include hproper hI in
theorem artin_first_generators [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    totalBetti k σ (artinModule k σ I) 1=idealGeneratorNumber k σ I :=
  (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso
    (artinFirstIdealIso k σ I hproper hI)).toLinearEquiv.finrank_eq)
end NSP14.Endpoint
