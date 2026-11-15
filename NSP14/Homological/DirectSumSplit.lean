module
public import NSP14.Homological.DirectSumHomology
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k : Type u) [Field k] (C : ℤ → ChainComplex (ModuleCat.{u} k) ℕ)

noncomputable def directSumInclusion (t : ℤ) : C t ⟶ directSumComplex k C where
  f i := colimit.ι ((familyComplex k C).X i) ⟨t⟩
  comm' i j _ := colimit.ι_map ((familyComplex k C).d i j) ⟨t⟩

noncomputable def directSumProjection (t : ℤ) : directSumComplex k C ⟶ C t where
  f i := Sigma.desc (Pi.single t (𝟙 ((C t).X i)))
  comm' i j _ := by
    apply colimit.hom_ext
    intro s
    change colimit.ι ((familyComplex k C).X i) s ≫
        Sigma.desc (Pi.single t (𝟙 ((C t).X i))) ≫ (C t).d i j =
      colimit.ι ((familyComplex k C).X i) s ≫ colim.map ((familyComplex k C).d i j) ≫
        Sigma.desc (Pi.single t (𝟙 ((C t).X j)))
    rw [colimit.ι_map_assoc]
    change Sigma.ι (fun a => (C a).X i) s.as ≫
        Sigma.desc (Pi.single t (𝟙 ((C t).X i))) ≫ (C t).d i j =
      (C s.as).d i j ≫ Sigma.ι (fun a => (C a).X j) s.as ≫
        Sigma.desc (Pi.single t (𝟙 ((C t).X j)))
    rw [←Category.assoc,Sigma.ι_comp_desc,Sigma.ι_comp_desc]
    by_cases h : s.as=t
    · subst t
      simp
    · simp [Pi.single_eq_of_ne h]

theorem directSumInclusion_projection (t : ℤ) :
    directSumInclusion k C t ≫ directSumProjection k C t=𝟙 (C t) := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact (Sigma.ι_comp_desc _ t).trans (by simp)

theorem directSumInclusion_projection_ne (s t : ℤ) (hst : s ≠ t) :
    directSumInclusion k C s ≫ directSumProjection k C t=0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact (Sigma.ι_comp_desc _ s).trans (by simp [Pi.single_eq_of_ne hst])

end NSP14.Homological
