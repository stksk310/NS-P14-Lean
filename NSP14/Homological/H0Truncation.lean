module
public import NSP14.Homological.ActionKoszulH0
public import NSP14.Homological.AcyclicQuotient
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ)

noncomputable def h0ProjectionZero : K.X 0 ⟶ K.homology 0 :=
  K.pOpcycles 0 ≫ (ChainComplex.isoHomologyι₀ K).inv

theorem h0ProjectionZero_comp : K.d 1 0 ≫ h0ProjectionZero R K=0 := by
  simp [h0ProjectionZero]

noncomputable def h0Projection : K ⟶ (ChainComplex.single₀ _).obj (K.homology 0) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨h0ProjectionZero R K,h0ProjectionZero_comp R K⟩

theorem h0Projection_f_zero : (h0Projection R K).f 0=h0ProjectionZero R K :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

noncomputable instance h0ProjectionZero_epi : Epi (h0ProjectionZero R K) := by
  unfold h0ProjectionZero
  infer_instance

noncomputable instance h0Projection_epi : Epi (h0Projection R K) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  cases i with
  | zero => rw [h0Projection_f_zero];exact h0ProjectionZero_epi R K
  | succ i =>
    exact IsZero.epi (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (K.homology 0) (i+1) (by omega)) _

theorem h0ProjectionZero_exact :
    (ShortComplex.mk _ _ (h0ProjectionZero_comp R K)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro a ha
  have hz : K.pOpcycles 0 a=0 := by
    have hq : h0ProjectionZero R K ≫ (ChainComplex.isoHomologyι₀ K).hom=K.pOpcycles 0 := by
      simp [h0ProjectionZero]
    have h := congrArg (fun z => (ChainComplex.isoHomologyι₀ K).hom z) ha
    simp only [map_zero] at h
    change (h0ProjectionZero R K ≫ (ChainComplex.isoHomologyι₀ K).hom).hom a=0 at h
    rw [hq] at h
    exact h
  have hm := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff (K.sc 0) a).mp hz
  have hp : (ComplexShape.down ℕ).prev 0=1 := by simp
  change a∈(K.d ((ComplexShape.down ℕ).prev 0) 0).hom.range at hm
  rw [hp] at hm
  exact hm

noncomputable instance h0Projection_quasiIso_zero : QuasiIsoAt (h0Projection R K) 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff,ShortComplex.quasiIso_iff_of_zeros']
  · change (ShortComplex.mk (K.d 1 0) ((h0Projection R K).f 0) _).Exact ∧ Epi ((h0Projection R K).f 0)
    simpa only [h0Projection_f_zero,ChainComplex.single₀_obj_zero] using And.intro (h0ProjectionZero_exact R K) (h0ProjectionZero_epi R K)
  · exact K.shape 0 0 (by simp [ComplexShape.down])
  all_goals rfl

noncomputable def h0KernelSequence : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  ShortComplex.mk (kernel.ι (h0Projection R K)) (h0Projection R K) (kernel.condition _)

theorem h0KernelSequence_shortExact : (h0KernelSequence R K).ShortExact := by
  unfold h0KernelSequence
  exact { exact := ShortComplex.exact_kernel _ }
end NSP14.Homological
