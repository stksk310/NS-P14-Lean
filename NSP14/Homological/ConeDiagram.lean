module
public import NSP14.Homological.ArrowCone
public import NSP14.Homological.KoszulExactness
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u w
variable (R : Type u) [CommRing R]
  {S T : ShortComplex (ChainComplex (ModuleCat.{w} R) ℕ)} (φ : S ⟶ T)

noncomputable def coneDiagramFirstArrow : Arrow.mk φ.τ₁ ⟶ Arrow.mk φ.τ₂ :=
  Arrow.homMk S.f T.f φ.comm₁₂.symm

noncomputable def coneDiagramSecondArrow : Arrow.mk φ.τ₂ ⟶ Arrow.mk φ.τ₃ :=
  Arrow.homMk S.g T.g φ.comm₂₃.symm

noncomputable def coneDiagram : ShortComplex (ChainComplex (ModuleCat.{w} R) ℕ) :=
  ShortComplex.mk
    ((arrowConeFunctor R).map (coneDiagramFirstArrow R φ))
    ((arrowConeFunctor R).map (coneDiagramSecondArrow R φ)) (by
      rw [← Functor.map_comp]
      have he : (coneDiagramFirstArrow R φ) ≫
          (coneDiagramSecondArrow R φ)=0 := by
        apply Arrow.hom_ext <;> simp [coneDiagramFirstArrow,coneDiagramSecondArrow,S.zero,T.zero]
      rw [he,Functor.map_zero])

noncomputable def coneDiagramZeroIso :
    (coneDiagram R φ).map (eval _ _ 0) ≅ T.map (eval _ _ 0) :=
  ShortComplex.isoMk (arrowConeZeroIso R φ.τ₁) (arrowConeZeroIso R φ.τ₂)
    (arrowConeZeroIso R φ.τ₃)
    (arrowCone_map_snd R (coneDiagramFirstArrow R φ) 0)
    (arrowCone_map_snd R (coneDiagramSecondArrow R φ) 0)

theorem arrowConePieceEquiv_natural {A B : Arrow (ChainComplex (ModuleCat.{w} R) ℕ)}
    (f : A ⟶ B) (i : ℕ) (a : (homotopyCofiber A.hom).X (i+1)) :
    arrowConePieceEquiv R B.hom i (((arrowConeFunctor R).map f).f (i+1) a)=
      (f.left.f i (arrowConePieceEquiv R A.hom i a).1,
        f.right.f (i+1) (arrowConePieceEquiv R A.hom i a).2) := by
  apply Prod.ext
  · exact congrArg (fun g => g.hom a) (arrowCone_map_fst R f i)
  · exact congrArg (fun g => g.hom a) (arrowCone_map_snd R f (i+1))

noncomputable def coneDiagramSuccIso (i : ℕ) :
    (coneDiagram R φ).map (eval _ _ (i+1)) ≅
      moduleProductShortComplex (S.map (eval _ _ i)) (T.map (eval _ _ (i+1))) :=
  ShortComplex.isoMk (arrowConePieceEquiv R φ.τ₁ i).toModuleIso
    (arrowConePieceEquiv R φ.τ₂ i).toModuleIso (arrowConePieceEquiv R φ.τ₃ i).toModuleIso
    (by
      apply ModuleCat.hom_ext
      ext a
      exact (arrowConePieceEquiv_natural R (coneDiagramFirstArrow R φ) i a).symm)
    (by
      apply ModuleCat.hom_ext
      ext a
      exact (arrowConePieceEquiv_natural R (coneDiagramSecondArrow R φ) i a).symm)

/-- Cones of an actual commutative diagram of short exact complexes remain
short exact. No chain finiteness is required, in particular for actual G. -/
theorem coneDiagram_shortExact (hS : S.ShortExact) (hT : T.ShortExact) :
    (coneDiagram R φ).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have hs := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  have ht := (HomologicalComplex.shortExact_iff_degreewise_shortExact T).mp hT
  cases i with
  | zero => exact ShortComplex.shortExact_of_iso (coneDiagramZeroIso R φ).symm (ht 0)
  | succ i =>
    exact ShortComplex.shortExact_of_iso (coneDiagramSuccIso R φ i).symm
      (moduleProductShortExact _ _ (hs i) (ht (i+1)))
end NSP14.Homological
