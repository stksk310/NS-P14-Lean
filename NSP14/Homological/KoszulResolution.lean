module

public import NSP14.Homological.KoszulPolynomialResolution
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k : Type u) (σ : Type u) [Field k] [Fintype σ]

/-- A choice of order on all variables, with no variable discarded. -/
noncomputable def variableList (_k : Type u) (σ : Type u) [Fintype σ] : List σ := List.ofFn (Fintype.equivFin σ).symm

omit [Field k] in
theorem variableList_nodup : (variableList k σ).Nodup := by
  exact List.nodup_ofFn.mpr (Fintype.equivFin σ).symm.injective

omit [Field k] in
theorem mem_variableList (x : σ) : x ∈ variableList k σ := by
  simp only [variableList, List.mem_ofFn]
  exact (Fintype.equivFin σ).symm.surjective x

omit [Field k] in
theorem variableList_length : (variableList k σ).length=Fintype.card σ := by
  simp [variableList]

/-- The actual coefficient field as P-module, through evaluation of every variable at zero. -/
noncomputable def residueField : ModuleCat (VariableRing k σ) :=
  (ModuleCat.restrictScalars (augmentation k σ).toRingHom).obj (ModuleCat.of k k)

noncomputable def augmentationLinear : VariableRing k σ →ₗ[VariableRing k σ] residueField k σ where
  toFun := augmentation k σ
  map_add' := map_add _
  map_smul' p q := map_mul (augmentation k σ) p q

theorem variablesIdeal_all_eq_ker : variablesIdeal k σ (variableList k σ) =
    (augmentationLinear k σ).ker := by
  classical
  ext p
  rw [variablesIdeal, MvPolynomial.mem_ideal_span_X_image]
  change (∀ d∈p.support, ∃ x∈variableList k σ, d x≠0) ↔ augmentation k σ p=0
  have he : augmentation k σ p = p.coeff 0 := by
    exact MvPolynomial.aeval_zero' p
  rw [he]
  constructor
  · intro h
    by_contra hn
    obtain ⟨x,_,hx⟩ := h 0 (MvPolynomial.mem_support_iff.mpr hn)
    exact hx ((by rfl))
  · intro h d hd
    have hn : d≠0 := by
      rintro rfl
      exact MvPolynomial.mem_support_iff.mp hd h
    have hex : ∃ x,d x≠0 := by
      by_contra hh
      push Not at hh
      exact hn (Finsupp.ext hh)
    obtain ⟨x,hx⟩ := hex
    exact ⟨x, mem_variableList k σ x, hx⟩

noncomputable def koszulAugmentationZero :
    (koszulList k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).X 0 ⟶
      residueField k σ := ModuleCat.ofHom (Y := residueField k σ)
  ((augmentationLinear k σ).comp (koszulZeroIso k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).hom.hom)

theorem koszulAugmentationZero_comp :
    (koszulList k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).d 1 0 ≫
      koszulAugmentationZero k σ = 0 := by
  apply ModuleCat.hom_ext
  ext a
  change augmentationLinear k σ (koszulZeroDifferential k σ (variableList k σ) _ a)=0
  apply (variablesIdeal_all_eq_ker k σ).le
  rw [← polynomial_variable_submodule, ← koszul_zero_boundary]
  exact ⟨a,rfl⟩

noncomputable def koszulAugmentation :
    koszulList k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) ⟶
      (ChainComplex.single₀ _).obj (residueField k σ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨koszulAugmentationZero k σ,koszulAugmentationZero_comp k σ⟩

theorem koszulAugmentationZero_surjective : Function.Surjective (koszulAugmentationZero k σ) := by
  intro a
  refine ⟨(koszulZeroIso k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).inv (MvPolynomial.C (show k from a)),?_⟩
  change augmentation k σ ((koszulZeroIso k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).hom
    ((koszulZeroIso k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).inv (MvPolynomial.C (show k from a))))=a
  rw [← ModuleCat.comp_apply, Iso.inv_hom_id]
  exact (augmentation k σ).commutes a

theorem koszulAugmentationZero_exact :
    (ShortComplex.mk _ _ (koszulAugmentationZero_comp k σ)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  apply (zero_boundary_membership k σ (variableList k σ) a).mp
  rw [variablesIdeal_all_eq_ker]
  exact ha

/-- The augmentation is a quasi-isomorphism by actual polynomial regularity and H₀ exactness. -/
theorem koszulAugmentation_quasiIso : QuasiIso (koszulAugmentation k σ) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
    · dsimp [koszulAugmentation]
      exact ⟨koszulAugmentationZero_exact k σ,
        (ModuleCat.epi_iff_surjective _).mpr (koszulAugmentationZero_surjective k σ)⟩
    · exact (koszulList k σ (variableList k σ) _).shape 0 0 (by simp [ComplexShape.down])
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact koszul_polynomial_exact_positive k σ _ (variableList_nodup k σ) n
    · apply ChainComplex.exactAt_succ_single_obj

/-- A genuine finite free resolution of the augmentation module, for ordinary derived Tor. -/
@[implicit_reducible]
noncomputable def koszulResolution : ProjectiveResolution (residueField k σ) where
  complex := koszulList k σ (variableList k σ) (ModuleCat.of (VariableRing k σ) (VariableRing k σ))
  projective i := by
    have := koszul_chain_free k σ (variableList k σ)
      (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) i
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis (VariableRing k σ) _)
  π := koszulAugmentation k σ
  quasiIso := koszulAugmentation_quasiIso k σ

end NSP14.Homological
