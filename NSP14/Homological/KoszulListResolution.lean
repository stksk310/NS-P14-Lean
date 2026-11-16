module
public import NSP14.Homological.KoszulTor
@[expose] public section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ] (xs : List σ) (hall : ∀ x : σ,x ∈ xs)

include hall in
theorem variablesIdeal_fullList_eq_ker : variablesIdeal k σ xs=(augmentationLinear k σ).ker := by
  rw [← variablesIdeal_all_eq_ker]
  unfold variablesIdeal
  congr 2
  ext x
  exact iff_of_true (hall x) (mem_variableList k σ x)

noncomputable def listKoszulAugmentationZero :
    (koszulList k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).X 0 ⟶ residueField k σ :=
  ModuleCat.ofHom (Y:=residueField k σ) ((augmentationLinear k σ).comp
    (koszulZeroIso k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).hom.hom)

include hall in
theorem listKoszulAugmentationZero_comp :
    (koszulList k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).d 1 0 ≫
      listKoszulAugmentationZero k σ xs=0 := by
  apply ModuleCat.hom_ext
  ext a
  change augmentationLinear k σ (koszulZeroDifferential k σ xs _ a)=0
  apply (variablesIdeal_fullList_eq_ker k σ xs hall).le
  rw [← polynomial_variable_submodule,← koszul_zero_boundary]
  exact ⟨a,rfl⟩

noncomputable def listKoszulAugmentation :
    koszulList k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) ⟶
      (ChainComplex.single₀ _).obj (residueField k σ) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨listKoszulAugmentationZero k σ xs,listKoszulAugmentationZero_comp k σ xs hall⟩

omit [Fintype σ] in
theorem listKoszulAugmentationZero_surjective : Function.Surjective (listKoszulAugmentationZero k σ xs) := by
  intro a
  refine ⟨(koszulZeroIso k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).inv
    (MvPolynomial.C (show k from a)),?_⟩
  change augmentation k σ ((koszulZeroIso k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).hom
    ((koszulZeroIso k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))).inv (MvPolynomial.C (show k from a))))=a
  rw [← ModuleCat.comp_apply,Iso.inv_hom_id]
  exact (augmentation k σ).commutes a

include hall in
theorem listKoszulAugmentationZero_exact :
    (ShortComplex.mk _ _ (listKoszulAugmentationZero_comp k σ xs hall)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  apply (zero_boundary_membership k σ xs a).mp
  rw [variablesIdeal_fullList_eq_ker k σ xs hall]
  exact ha

theorem listKoszulAugmentation_quasiIso (hxs : xs.Nodup) : QuasiIso (listKoszulAugmentation k σ xs hall) := by
  refine ⟨fun n => ?_⟩
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
    · dsimp [listKoszulAugmentation]
      exact ⟨listKoszulAugmentationZero_exact k σ xs hall,
        (ModuleCat.epi_iff_surjective _).mpr (listKoszulAugmentationZero_surjective k σ xs)⟩
    · exact (koszulList k σ xs _).shape 0 0 (by simp [ComplexShape.down])
    all_goals rfl
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact koszul_polynomial_exact_positive k σ xs hxs n
    · apply ChainComplex.exactAt_succ_single_obj

/-- Any complete nonrepeating variable order gives an actual free
resolution of k. This is an ordinary Tor comparison, not a declaration
that a reordered complex computes the same numbers. -/
@[implicit_reducible]
noncomputable def listKoszulResolution (hxs : xs.Nodup) : ProjectiveResolution (residueField k σ) where
  complex := koszulList k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ))
  projective i := by
    have := koszul_chain_free k σ xs (ModuleCat.of (VariableRing k σ) (VariableRing k σ)) i
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis (VariableRing k σ) _)
  π := listKoszulAugmentation k σ xs hall
  quasiIso := listKoszulAugmentation_quasiIso k σ xs hall hxs

noncomputable def fullListTorKoszulIso (hxs : xs.Nodup) (M : ModuleCat (VariableRing k σ)) (i : ℕ) :
    (((CategoryTheory.Tor (ModuleCat (VariableRing k σ)) i).obj M).obj (residueField k σ)) ≅
      koszulHomology k σ xs M i :=
  (listKoszulResolution k σ xs hall hxs).isoLeftDerivedObj ((tensoringLeft _).obj M) i ≪≫
    (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (tensorKoszulIso k σ xs M)
end NSP14.Homological
