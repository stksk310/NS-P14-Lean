module
public import NSP14.Endpoint.StandardArtinGenerators
public import NSP14.Homological.FreeKoszulHomology
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
namespace NSP14.Width
variable (k σ : Type) [Field k] [Fintype σ]

theorem idealGeneratorNumber_le (I : Ideal (MvPolynomial σ k)) {ι : Type} [Fintype ι]
    (v : ι → MvPolynomial σ k) (hI : I=Ideal.span (Set.range v)) :
    NSP14.Endpoint.idealGeneratorNumber k σ I ≤ Fintype.card ι := by
  let w : ι → I := fun i => ⟨v i,hI ▸ Ideal.subset_span ⟨i,rfl⟩⟩
  let f := Finsupp.linearCombination (MvPolynomial σ k) w
  have hsurj : Function.Surjective f := by
    intro a
    have ha : a.val∈Submodule.span (MvPolynomial σ k) (Set.range v) := by
      change a.val∈Ideal.span (Set.range v)
      rw [←hI]
      exact a.property
    obtain ⟨c,hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp ha
    refine ⟨c,?_⟩
    apply Subtype.ext
    simpa only [f,Finsupp.linearCombination_apply,Finsupp.sum,Submodule.coe_sum,Submodule.coe_smul,w] using hc
  let F : ModuleCat (VariableRing k σ) := ModuleCat.of _ (ι →₀ VariableRing k σ)
  let g : F ⟶ NSP14.Endpoint.artinIdealModule k σ I := ModuleCat.ofHom f
  let : Epi g := (ModuleCat.epi_iff_surjective g).mpr hsurj
  have hb := totalBetti_zero_le_of_epi k σ g
  rw [minimalFreeRank_at_zero k σ F (Finsupp.basisSingleOne)] at hb
  exact hb
end NSP14.Width
