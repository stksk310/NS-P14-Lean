module
public import NSP14.Homological.GradedKoszulMap
public import NSP14.Homological.QuotientBettiAdditivity
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]
  (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
  (G1 : GradedPolynomialModule k σ S.X₁) (G2 : GradedPolynomialModule k σ S.X₂)
  (G3 : GradedPolynomialModule k σ S.X₃)
  (hf : ∀ q (a : coefficientModule k σ S.X₁),a ∈ G1.degreeSpace q → S.f a ∈ G2.degreeSpace q)
  (hg : ∀ q (a : coefficientModule k σ S.X₂),a ∈ G2.degreeSpace q → S.g a ∈ G3.degreeSpace q)

noncomputable def gradedKoszulSequenceLeft (xs : List σ) (t : ℤ) :
    gradedKoszulComplex k σ S.X₁ G1 xs t ⟶ gradedKoszulComplex k σ S.X₂ G2 xs (t+0) :=
  gradedKoszulMap k σ G1 G2 S.f 0 (by simpa only [add_zero] using hf) xs t

noncomputable def gradedKoszulSequenceRight (xs : List σ) (t : ℤ) :
    gradedKoszulComplex k σ S.X₂ G2 xs (t+0) ⟶ gradedKoszulComplex k σ S.X₃ G3 xs ((t+0)+0) :=
  gradedKoszulMap k σ G2 G3 S.g 0 (by simpa only [add_zero] using hg) xs (t+0)

theorem gradedKoszulSequence_comp (xs : List σ) (t : ℤ) :
    gradedKoszulSequenceLeft k σ S G1 G2 hf xs t ≫ gradedKoszulSequenceRight k σ S G2 G3 hg xs t=0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  let F := coefficientKoszulListFunctor k σ xs
  have hz : F.map S.f ≫ F.map S.g=0 := by rw [←F.map_comp,S.zero,F.map_zero]
  exact congrArg (fun h => (h.f i).hom a.val) hz

noncomputable def gradedKoszulSequence (xs : List σ) (t : ℤ) :
    ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ) :=
  ShortComplex.mk (gradedKoszulSequenceLeft k σ S G1 G2 hf xs t)
    (gradedKoszulSequenceRight k σ S G2 G3 hg xs t) (gradedKoszulSequence_comp k σ S G1 G2 G3 hf hg xs t)

/-- Restrict an actual short exact module sequence to each internal
degree. Preimages are projected with the constructed natural retractions. -/
theorem gradedKoszulSequence_shortExact (hS : S.ShortExact) (xs : List σ) (t : ℤ) :
    (gradedKoszulSequence k σ S G1 G2 G3 hf hg xs t).ShortExact := by
  have ht := coefficientKoszulListFunctor_shortExact k σ xs S hS
  have hti := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp ht
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    have haz : (((coefficientKoszulListFunctor k σ xs).map S.g).f i).hom a.val=0 :=
      congrArg Subtype.val ha
    obtain ⟨b,hb⟩ := (ShortComplex.moduleCat_exact_iff _).mp (hti i).exact a.val haz
    refine ⟨((gradedKoszulRetraction k σ S.X₁ G1 xs t).f i).hom b,?_⟩
    have hn := congrArg (fun h => (h.f i).hom b)
      (gradedKoszulMap_retraction k σ G1 G2 S.f 0 (by simpa only [add_zero] using hf) xs t)
    change ((gradedKoszulRetraction k σ S.X₂ G2 xs (t+0)).f i).hom
        ((((coefficientKoszulListFunctor k σ xs).map S.f).f i).hom b)=
      ((gradedKoszulSequenceLeft k σ S G1 G2 hf xs t).f i).hom
        (((gradedKoszulRetraction k σ S.X₁ G1 xs t).f i).hom b) at hn
    have hrb := congrArg (fun z => ((gradedKoszulRetraction k σ S.X₂ G2 xs (t+0)).f i).hom z) hb
    have hs := congrArg (fun h => (h.f i).hom a)
      (gradedKoszulInclusion_retraction k σ S.X₂ G2 xs (t+0))
    exact hn.symm.trans (hrb.trans hs)
  · rw [ModuleCat.mono_iff_injective]
    intro a b hab
    have h := congrArg Subtype.val hab
    have hinj := (ModuleCat.mono_iff_injective _).mp (hti i).mono_f
    apply Subtype.ext
    exact hinj h
  · rw [ModuleCat.epi_iff_surjective]
    intro a
    obtain ⟨b,hb⟩ := (ModuleCat.epi_iff_surjective _).mp (hti i).epi_g a.val
    refine ⟨((gradedKoszulRetraction k σ S.X₂ G2 xs (t+0)).f i).hom b,?_⟩
    have hn := congrArg (fun h => (h.f i).hom b)
      (gradedKoszulMap_retraction k σ G2 G3 S.g 0 (by simpa only [add_zero] using hg) xs (t+0))
    change ((gradedKoszulRetraction k σ S.X₃ G3 xs ((t+0)+0)).f i).hom
        ((((coefficientKoszulListFunctor k σ xs).map S.g).f i).hom b)=
      ((gradedKoszulSequenceRight k σ S G2 G3 hg xs t).f i).hom
        (((gradedKoszulRetraction k σ S.X₂ G2 xs (t+0)).f i).hom b) at hn
    have hrb := congrArg (fun z => ((gradedKoszulRetraction k σ S.X₃ G3 xs ((t+0)+0)).f i).hom z) hb
    have hs := congrArg (fun h => (h.f i).hom a)
      (gradedKoszulInclusion_retraction k σ S.X₃ G3 xs ((t+0)+0))
    exact hn.symm.trans (hrb.trans hs)

variable [Fintype σ]
  [Module.Finite (VariableRing k σ) S.X₁]
  [Module.Finite (VariableRing k σ) S.X₂]
  [Module.Finite (VariableRing k σ) S.X₃]

include hf hg in
/-- Actual internal-degree Betti additivity from the actual degreewise
short exact sequence and the proved zero map on total homology. -/
theorem graded_quotient_betti_additivity (hS : S.ShortExact)
    (hz : ∀ j,homologyMap ((coefficientKoszulFunctor k σ).map S.f) j=0) (i : ℕ) (t : ℤ) :
    gradedBetti k σ S.X₃ G3 (i+1) t=
      gradedBetti k σ S.X₂ G2 (i+1) t+gradedBetti k σ S.X₁ G1 i t := by
  let T := gradedKoszulSequence k σ S G1 G2 G3 hf hg (variableList k σ) t
  have hT := gradedKoszulSequence_shortExact k σ S G1 G2 G3 hf hg hS (variableList k σ) t
  let : Module.Finite k (T.X₂.homology (i+1)) := by
    change Module.Finite k ((gradedKoszulComplex k σ S.X₂ G2 (variableList k σ) (t+0)).homology (i+1))
    infer_instance
  let : Module.Finite k (T.X₃.homology (i+1)) := by
    change Module.Finite k ((gradedKoszulComplex k σ S.X₃ G3 (variableList k σ) ((t+0)+0)).homology (i+1))
    infer_instance
  let : Module.Finite k (T.X₁.homology i) := by
    change Module.Finite k ((gradedKoszulComplex k σ S.X₁ G1 (variableList k σ) t).homology i)
    infer_instance
  have hzero : ∀ j,homologyMap T.f j=0 := by
    intro j
    exact gradedKoszulMap_homology_zero k σ G1 G2 S.f 0 (by simpa only [add_zero] using hf)
      (variableList k σ) t j (hz j)
  have h := homology_quotient_additivity k T hT i (hzero (i+1)) (hzero i)
  change gradedBetti k σ S.X₃ G3 (i+1) ((t+0)+0)=
    gradedBetti k σ S.X₂ G2 (i+1) (t+0)+gradedBetti k σ S.X₁ G1 i t at h
  simpa only [add_zero] using h

end NSP14.Homological
