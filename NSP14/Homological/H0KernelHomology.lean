module
public import NSP14.Homological.H0Truncation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ)

theorem h0Single_homology_positive (i : ℕ) :
    IsZero (((ChainComplex.single₀ (ModuleCat R)).obj (K.homology 0)).homology (i+1)) :=
  HomologicalComplex.ExactAt.isZero_homology (ChainComplex.exactAt_succ_single_obj (K.homology 0) i)

/-- Removing only H0 leaves every positive homology group unchanged. -/
noncomputable def h0KernelHomologyPositiveIso (i : ℕ) :
    (h0KernelSequence R K).X₁.homology (i+1) ≅ K.homology (i+1) := by
  let S := h0KernelSequence R K
  have hS := h0KernelSequence_shortExact R K
  let : Mono (homologyMap S.f (i+1)) :=
    (hS.homology_exact₁ (i+2) (i+1) rfl).mono_g ((h0Single_homology_positive R K (i+1)).eq_of_src _ _)
  let : Epi (homologyMap S.f (i+1)) :=
    (hS.homology_exact₂ (i+1)).epi_f ((h0Single_homology_positive R K i).eq_of_tgt _ _)
  let : IsIso (homologyMap S.f (i+1)) := isIso_of_mono_of_epi _
  exact asIso (homologyMap S.f (i+1))

theorem h0KernelHomologyZero : IsZero ((h0KernelSequence R K).X₁.homology 0) := by
  let S := h0KernelSequence R K
  have hS := h0KernelSequence_shortExact R K
  let : Mono (homologyMap S.f 0) :=
    (hS.homology_exact₁ 1 0 rfl).mono_g ((h0Single_homology_positive R K 0).eq_of_src _ _)
  let : IsIso (homologyMap S.g 0) :=
    (quasiIsoAt_iff_isIso_homologyMap (h0Projection R K) 0).mp (h0Projection_quasiIso_zero R K)
  have hz : homologyMap S.f 0=0 := by
    rw [← cancel_mono (homologyMap S.g 0),← homologyMap_comp,S.zero,homologyMap_zero,zero_comp]
  rw [IsZero.iff_id_eq_zero]
  apply (cancel_mono (homologyMap S.f 0)).mp
  simpa only [Category.id_comp,zero_comp] using hz
end NSP14.Homological
