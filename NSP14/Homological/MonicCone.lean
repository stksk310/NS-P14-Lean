module
public import NSP14.Homological.ConeSuspension
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R]
  (S : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)

noncomputable def acyclicKernelHomologyIso (h₁ : ∀ i,IsZero (S.X₁.homology i)) (i : ℕ) :
    S.X₂.homology i ≅ S.X₃.homology i := by
  let : Mono (homologyMap S.g i) := (hS.homology_exact₂ i).mono_g ((h₁ i).eq_of_src _ _)
  have hepi : Epi (homologyMap S.g i) := by
    cases i with
    | zero =>
      let : Epi (S.g.f 0) := ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS 0).epi_g
      exact epi_homologyMap_of_epi_of_not_rel S.g 0 (by intro j h;change j+1=0 at h;omega)
    | succ i => exact (hS.homology_exact₃ (i+1) i rfl).epi_f ((h₁ i).eq_of_tgt _ _)
  let : IsIso (homologyMap S.g i) := isIso_of_mono_of_epi _
  exact asIso (homologyMap S.g i)

noncomputable def monicConeDiagram : idZeroSequence R S.X₁ ⟶ S :=
  ShortComplex.homMk (𝟙 _) S.f 0 (by simp [idZeroSequence]) (by simp [idZeroSequence,S.zero])

noncomputable def monicConeHomologyIso (i : ℕ) : (homotopyCofiber S.f).homology i ≅ S.X₃.homology i := by
  let D := coneDiagram R (monicConeDiagram R S)
  have hD := coneDiagram_shortExact R (monicConeDiagram R S) (idZeroSequence_shortExact R S.X₁) hS
  exact acyclicKernelHomologyIso R D hD (identityCone_homology_isZero R S.X₁) i ≪≫
    (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (zeroArrowConeIso R S.X₃)
end NSP14.Homological
