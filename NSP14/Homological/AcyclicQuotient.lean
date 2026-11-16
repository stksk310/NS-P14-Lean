module
public import NSP14.Homological.ConeSuspension
@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject
namespace NSP14.Homological
universe u w
variable (R : Type u) [CommRing R]
  (S : ShortComplex (ChainComplex (ModuleCat.{w} R) ℕ)) (hS : S.ShortExact)

/-- Acyclic quotient gives an actual homology isomorphism, with no chain
finiteness assumptions. -/
noncomputable def acyclicQuotientHomologyIso
    (h₃ : ∀ i,IsZero (S.X₃.homology i)) (i : ℕ) : S.X₁.homology i ≅ S.X₂.homology i := by
  let : Mono (homologyMap S.f i) :=
    (hS.homology_exact₁ (i+1) i (natDownStep i)).mono_g ((h₃ (i+1)).eq_of_src _ _)
  let : Epi (homologyMap S.f i) := (hS.homology_exact₂ i).epi_f ((h₃ i).eq_of_tgt _ _)
  let : IsIso (homologyMap S.f i) := isIso_of_mono_of_epi _
  exact asIso (homologyMap S.f i)

noncomputable def epiConeDiagram : S ⟶ zeroIdSequence R S.X₃ :=
  ShortComplex.homMk 0 S.g (𝟙 _) (by
    change (0 : S.X₁ ⟶ (0 : ChainComplex (ModuleCat.{w} R) ℕ)) ≫
      (0 : (0 : ChainComplex (ModuleCat.{w} R) ℕ) ⟶ S.X₃)=S.f ≫ S.g
    rw [zero_comp,S.zero]) (by simp [zeroIdSequence])

noncomputable def epiConeKernelHomologyIso (i : ℕ) :
    (homotopyCofiber S.g).homology i ≅ (coneSuspension R S.X₁).homology i := by
  let h := coneDiagram_shortExact R (epiConeDiagram R S) hS (zeroIdSequence_shortExact R S.X₃)
  exact (acyclicQuotientHomologyIso R _ h (identityCone_homology_isZero R S.X₃) i).symm

noncomputable def epiConeHomologySuccIso (i : ℕ) :
    (homotopyCofiber S.g).homology (i+1) ≅ S.X₁.homology i :=
  epiConeKernelHomologyIso R S hS (i+1) ≪≫ coneSuspensionHomologyIso R S.X₁ i

include hS in
theorem epiCone_homology_zero : IsZero ((homotopyCofiber S.g).homology 0) :=
  IsZero.of_iso (coneSuspension_homology_zero R S.X₁) (epiConeKernelHomologyIso R S hS 0)
end NSP14.Homological
