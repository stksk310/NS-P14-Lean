module

public import NSP14.Homological.KoszulH0Naturality
public import NSP14.Homological.KoszulLongExact

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]

/-- An actual minimal finite-free resolution given as its syzygy short exact covers.
No Betti comparison or homology dimension is a field of this data. -/
structure MinimalFreeTower (M : ModuleCat.{u} (VariableRing k σ)) where
  Z : ℕ → ModuleCat.{u} (VariableRing k σ)
  Q : ℕ → ModuleCat.{u} (VariableRing k σ)
  rank : ℕ → ℕ
  basis : ∀ i,Module.Basis (ULift.{u} (Fin (rank i))) (VariableRing k σ) (Q i)
  start : Z 0 ≅ M
  inc : ∀ i,Z (i+1) ⟶ Q i
  cover : ∀ i,Q i ⟶ Z i
  zero : ∀ i,inc i ≫ cover i=0
  exact : ∀ i,(ShortComplex.mk (inc i) (cover i) (zero i)).ShortExact
  minimal : ∀ i (z : Z (i+1)),inc i z∈koszulVariableSubmodule k σ (variableList k σ) (Q i)

namespace MinimalFreeTower

variable {k σ} {M : ModuleCat.{u} (VariableRing k σ)} (T : MinimalFreeTower k σ M)

noncomputable instance free_Q (i : ℕ) : Module.Free (VariableRing k σ) (T.Q i) :=
  Module.Free.of_basis (T.basis i)

noncomputable instance finite_Q (i : ℕ) : Module.Finite (VariableRing k σ) (T.Q i) :=
  Module.Finite.of_basis (T.basis i)

noncomputable instance finite_Z (i : ℕ) : Module.Finite (VariableRing k σ) (T.Z i) :=
  Module.Finite.of_surjective (T.cover i).hom (T.exact i).moduleCat_surjective_g

noncomputable def sequence (i : ℕ) : ShortComplex (ModuleCat.{u} (VariableRing k σ)) :=
  ShortComplex.mk (T.inc i) (T.cover i) (T.zero i)

/-- The chain complex underlying the syzygy covers is an actual free resolution. -/
noncomputable def complex : ChainComplex (ModuleCat.{u} (VariableRing k σ)) ℕ :=
  ChainComplex.of T.Q (fun i => T.cover (i+1) ≫ T.inc i) (by
    intro i
    simp only [Category.assoc]
    rw [← Category.assoc (T.inc (i+1)),T.zero]
    simp)

noncomputable def augmentation : T.complex ⟶ (ChainComplex.single₀ _).obj M :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨T.cover 0 ≫ T.start.hom,by
    change (T.cover 1 ≫ T.inc 0) ≫ T.cover 0 ≫ T.start.hom=0
    simp only [Category.assoc]
    rw [← Category.assoc (T.inc 0),T.zero]
    simp⟩

theorem complex_exact_positive (i : ℕ) : T.complex.ExactAt (i+1) := by
  rw [HomologicalComplex.exactAt_iff' _ (i+2) (i+1) i ((ComplexShape.down ℕ).prev_eq' rfl) ((ComplexShape.down ℕ).next_eq' rfl)]
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  have hz : T.cover (i+1) a=0 := (T.exact i).moduleCat_injective_f (by
    simpa [complex,ChainComplex.of_d] using ha)
  obtain ⟨b,hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp (T.exact (i+1)).exact _ hz
  obtain ⟨c,hc⟩ := (T.exact (i+2)).moduleCat_surjective_g b
  refine ⟨c,?_⟩
  change (T.complex.d (i+2) (i+1)) c=a
  change (ChainComplex.of.d T.Q (fun j => T.cover (j+1) ≫ T.inc j) (i+2) (i+1)) c=a
  erw [ChainComplex.of_d]
  change T.inc (i+1) (T.cover (i+1+1) c)=a
  rw [hc,hb]

noncomputable def toProjectiveResolution : ProjectiveResolution M where
  complex := T.complex
  projective i := ModuleCat.projective_of_free (T.basis i)
  π := T.augmentation
  quasiIso := by
    refine ⟨fun i => ?_⟩
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
      · refine ⟨?_,?_⟩
        · rw [ShortComplex.moduleCat_exact_iff]
          intro a ha
          have hz : T.cover 0 a=0 := by
            apply (ModuleCat.mono_iff_injective T.start.hom).mp inferInstance
            rw [map_zero]
            change T.augmentation.f 0 a=0 at ha
            erw [augmentation,ChainComplex.toSingle₀Equiv_symm_apply_f_zero] at ha
            exact ha
          obtain ⟨b,hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp (T.exact 0).exact _ hz
          obtain ⟨c,hc⟩ := (T.exact 1).moduleCat_surjective_g b
          exact ⟨c,by change T.inc 0 (T.cover 1 c)=a; rw [hc,hb]⟩
        · exact (ModuleCat.epi_iff_surjective _).mpr
            (T.start.toLinearEquiv.surjective.comp (T.exact 0).moduleCat_surjective_g)
      · exact T.complex.shape 0 0 (by simp [ComplexShape.down])
      all_goals rfl
    | succ i =>
      rw [quasiIsoAt_iff_exactAt']
      · exact T.complex_exact_positive i
      · apply ChainComplex.exactAt_succ_single_obj

theorem h0_inc_zero (i : ℕ) : (koszulHomologyFunctor k σ (variableList k σ) 0).map (T.inc i)=0 :=
  koszul_h0_map_zero_of_minimal k σ _ _ (T.minimal i)

/-- Dimension shifting is proved by the actual Koszul long exact sequence of each cover. -/
noncomputable def syzygyHomologyIso (i j : ℕ) :
    koszulHomology k σ (variableList k σ) (T.Z i) (j+1) ≅
      koszulHomology k σ (variableList k σ) (T.Z (i+1)) j := by
  let hS := koszul_shortExact k σ (variableList k σ) (T.sequence i) (T.exact i)
  let d := hS.δ (j+1) j rfl
  letI hm : Mono d := hS.mono_δ _ _ rfl (freeKoszulHomology_positive k σ (T.Q i) j)
  letI he : Epi d := by
    cases j with
    | zero =>
      exact (hS.homology_exact₁ 1 0 rfl).epi_f_iff.mpr (T.h0_inc_zero i)
    | succ j => exact hS.epi_δ _ _ rfl (freeKoszulHomology_positive k σ (T.Q i) j)
  letI := isIso_of_mono_of_epi d
  exact asIso d

noncomputable def h0CoverIso (i : ℕ) :
    koszulHomology k σ (variableList k σ) (T.Q i) 0 ≅
      koszulHomology k σ (variableList k σ) (T.Z i) 0 := by
  let hS := koszul_shortExact k σ (variableList k σ) (T.sequence i) (T.exact i)
  let g := (koszulHomologyFunctor k σ (variableList k σ) 0).map (T.cover i)
  letI hm : Mono g := (hS.homology_exact₂ 0).mono_g_iff.mpr (T.h0_inc_zero i)
  let : Epi ((koszulFunctor k σ (variableList k σ)).map (T.cover i)) := hS.epi_g
  letI he : Epi g := epi_homologyMap_of_epi_of_not_rel _ 0 (by intro j h; change j+1=0 at h; omega)
  letI := isIso_of_mono_of_epi g
  exact asIso g

noncomputable def iteratedSyzygyIso (i j : ℕ) :
    koszulHomology k σ (variableList k σ) (T.Z i) j ≅
      koszulHomology k σ (variableList k σ) (T.Z (i+j)) 0 := by
  induction j generalizing i with
  | zero => exact Iso.refl _
  | succ j ih =>
    have e := T.syzygyHomologyIso i j ≪≫ ih (i+1)
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using e

noncomputable def homologyRankBasisIso (i : ℕ) :
    koszulHomologyK k σ M i ≅ ModuleCat.of k (ULift.{u} (Fin (T.rank i)) →₀ k) := by
  let e0 : koszulHomology k σ (variableList k σ) M i ≅
      koszulHomology k σ (variableList k σ) (T.Z 0) i :=
    koszulHomologyIso k σ (variableList k σ) i T.start.symm
  let e1 : koszulHomology k σ (variableList k σ) (T.Z 0) i ≅
      koszulHomology k σ (variableList k σ) (T.Z i) 0 := by
    simpa only [Nat.zero_add] using T.iteratedSyzygyIso 0 i
  let e := e0 ≪≫ e1 ≪≫ (T.h0CoverIso i).symm
  exact (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso e ≪≫
    freeKoszulH0BasisIso k σ (T.Q i) (T.basis i)

end MinimalFreeTower

/-- The rank of every stage of an actual minimal free resolution equals ordinary Betti,
proved by syzygy covers rather than assuming a balancing comparison theorem. -/
theorem minimalResolutionBetti {M : ModuleCat.{u} (VariableRing k σ)}
    [Module.Finite (VariableRing k σ) M] (T : MinimalFreeTower k σ M) (i : ℕ) :
    totalBetti k σ M i=T.rank i := by
  rw [totalBetti,(T.homologyRankBasisIso i).toLinearEquiv.finrank_eq,Module.finrank_finsupp_self]
  simp

end NSP14.Homological
