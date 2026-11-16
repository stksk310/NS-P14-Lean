module
public import NSP14.Homological.NativeKoszulExact
public import NSP14.Homological.MonicCone
public import NSP14.Homological.RegularActionCoefficient
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R] (r : R)

noncomputable def scalarQuotientModule : ModuleCat.{u} R := ModuleCat.of R (R ⧸ Ideal.span {r})

noncomputable def scalarQuotientProjection : ModuleCat.of R R ⟶ scalarQuotientModule R r :=
  ModuleCat.ofHom (X:=ModuleCat.of R R) (Y:=scalarQuotientModule R r)
    (Ideal.Quotient.mkₐ R (Ideal.span {r})).toLinearMap

theorem scalarQuotient_comp : (r • 𝟙 (ModuleCat.of R R)) ≫ scalarQuotientProjection R r=0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change Ideal.Quotient.mk (Ideal.span {r}) (r*a)=0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mul_mem_right a _ (Ideal.subset_span (Set.mem_singleton _))

noncomputable def scalarQuotientSequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (r • 𝟙 (ModuleCat.of R R)) (scalarQuotientProjection R r) (scalarQuotient_comp R r)

theorem scalarQuotientSequence_shortExact (hr : Function.Injective (fun a : R => r*a)) :
    (scalarQuotientSequence R r).ShortExact := by
  unfold scalarQuotientSequence
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    intro a ha
    have hm : a∈Ideal.span {r} := Ideal.Quotient.eq_zero_iff_mem.mp ha
    obtain ⟨b,hb⟩ := Ideal.mem_span_singleton'.mp hm
    exact ⟨b,(mul_comm r b).trans hb⟩
  · rw [ModuleCat.mono_iff_injective]
    exact hr
  · rw [ModuleCat.epi_iff_surjective]
    exact Ideal.Quotient.mk_surjective

variable (k : Type u) [Field k] [Algebra k R]
/-- Koszul reduction by an actual regular element; there is no assumed
spectral-sequence degeneration and no finite-chain hypothesis. -/
noncomputable def regularElementCoefficientReductionIso (rs : List R)
    (hr : Function.Injective (fun a : R => r*a)) (i : ℕ) :
    (regularPartialCoefficientComplex k R (r::rs)).homology i ≅
      (actionCoefficientComplex k R rs (scalarQuotientModule R r)).homology i := by
  let S := (scalarQuotientSequence R r).map (actionCoefficientFunctor R k rs)
  have hS := actionCoefficientFunctor_shortExact R k rs _ (scalarQuotientSequence_shortExact R r hr)
  exact (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (actionCoefficientConsIso R k r rs (ModuleCat.of R R)) ≪≫
    monicConeHomologyIso k S hS i
end NSP14.Homological
