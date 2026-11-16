module
public import NSP14.Homological.GradedKoszulSplit
public import NSP14.Homological.CoefficientKoszulListFunctor
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]
  {M N : ModuleCat.{u} (VariableRing k σ)}
  (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule k σ N)

/-- Restrict the actual Koszul map, with its proved coefficient-degree
shift, to the actual internal-degree complexes. -/
noncomputable def gradedKoszulMap (f : M ⟶ N) (s : ℤ)
    (hf : ∀ q (a : coefficientModule k σ M),a ∈ G.degreeSpace q → f a ∈ H.degreeSpace (q+s))
    (xs : List σ) (t : ℤ) :
    gradedKoszulComplex k σ M G xs t ⟶ gradedKoszulComplex k σ N H xs (t+s) :=
  ChainComplex.ofHom (fun i => ModuleCat.ofHom
    (LinearMap.codRestrict (gradedKoszulSpace k σ N H xs (t+s) i)
      ((coefficientMap k σ ((koszulMap k σ xs f).f i)).comp
        (gradedKoszulSpace k σ M G xs t i).subtype) (by
          intro a
          have h := koszulMap_homogeneous k σ G H f s hf xs i (t-(i:ℤ)) a.val a.property
          have he : t-(i:ℤ)+s=(t+s)-(i:ℤ) := by omega
          change (koszulMap k σ xs f).f i a.val ∈
            (koszulChainGrading k σ N H xs i).degreeSpace ((t+s)-(i:ℤ))
          rw [←he]
          exact h))) (by
    intro i
    simp only [gradedKoszulComplex,ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    exact congrArg (fun h => h.hom a.val) ((koszulMap k σ xs f).comm (i+1) i))

@[reassoc]
theorem gradedKoszulMap_inclusion (f : M ⟶ N) (s : ℤ)
    (hf : ∀ q (a : coefficientModule k σ M),a ∈ G.degreeSpace q → f a ∈ H.degreeSpace (q+s))
    (xs : List σ) (t : ℤ) :
    gradedKoszulMap k σ G H f s hf xs t ≫ gradedKoszulInclusion k σ N H xs (t+s)=
      gradedKoszulInclusion k σ M G xs t ≫ (coefficientKoszulListFunctor k σ xs).map f := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- Zero on the same actual total homology implies zero on every
internal-degree summand, using the constructed split inclusion. -/
theorem gradedKoszulMap_homology_zero (f : M ⟶ N) (s : ℤ)
    (hf : ∀ q (a : coefficientModule k σ M),a ∈ G.degreeSpace q → f a ∈ H.degreeSpace (q+s))
    (xs : List σ) (t : ℤ) (i : ℕ)
    (hz : homologyMap ((coefficientKoszulListFunctor k σ xs).map f) i=0) :
    homologyMap (gradedKoszulMap k σ G H f s hf xs t) i=0 := by
  have hc := congrArg (fun h => homologyMap h i) (gradedKoszulMap_inclusion k σ G H f s hf xs t)
  rw [homologyMap_comp,homologyMap_comp,hz,comp_zero] at hc
  let : Mono (homologyMap (gradedKoszulInclusion k σ N H xs (t+s)) i) :=
    (ModuleCat.mono_iff_injective _).mpr (gradedKoszulHomologyInclusion_injective k σ N H xs (t+s) i)
  apply (cancel_mono (homologyMap (gradedKoszulInclusion k σ N H xs (t+s)) i)).mp
  rw [zero_comp]
  exact hc

/-- The constructed degree projections commute with actual homogeneous
maps. The proof checks every summand of the actual direct decomposition. -/
theorem gradedKoszulMap_retraction (f : M ⟶ N) (s : ℤ)
    (hf : ∀ q (a : coefficientModule k σ M),a ∈ G.degreeSpace q → f a ∈ H.degreeSpace (q+s))
    (xs : List σ) (t : ℤ) :
    (coefficientKoszulListFunctor k σ xs).map f ≫ gradedKoszulRetraction k σ N H xs (t+s)=
      gradedKoszulRetraction k σ M G xs t ≫ gradedKoszulMap k σ G H f s hf xs t := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply (cancel_epi (gradedKoszulSumPieceIso k σ M G xs i).hom).mp
  apply colimit.hom_ext
  intro u
  simp only [comp_f]
  rw [gradedKoszulSumPieceIso_inclusion_assoc,gradedKoszulSumPieceIso_inclusion_assoc]
  have he : gradedKoszulInclusion k σ M G xs u.as ≫
        (coefficientKoszulListFunctor k σ xs).map f ≫ gradedKoszulRetraction k σ N H xs (t+s)=
      gradedKoszulInclusion k σ M G xs u.as ≫ gradedKoszulRetraction k σ M G xs t ≫
        gradedKoszulMap k σ G H f s hf xs t := by
    rw [←gradedKoszulMap_inclusion_assoc k σ G H f s hf xs u.as]
    by_cases hut : u.as=t
    · subst t
      rw [gradedKoszulInclusion_retraction,Category.comp_id,gradedKoszulInclusion_retraction_assoc]
    · have hus : u.as+s ≠ t+s := fun h => hut (add_right_cancel h)
      rw [gradedKoszulInclusion_retraction_ne k σ N H xs (u.as+s) (t+s) hus,comp_zero,
        gradedKoszulInclusion_retraction_ne_assoc k σ M G xs u.as t hut,zero_comp]
  simpa only [comp_f,Category.assoc] using congrArg (fun h => h.f i) he

end NSP14.Homological
