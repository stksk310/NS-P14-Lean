module
public import NSP14.Semigroup.TruncGradingCoordinates
public import NSP14.Semigroup.CutGeneratorCount
public import NSP14.Ordinary.CutFinite
public import NSP14.Homological.CoordinateGrading
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open NSP14.Homological CategoryTheory
open scoped Classical
namespace NSP14.NumericalSemigroup.LinearCutData
variable {S : NumericalSemigroup} {k : Type} [Field k] (C : S.LinearCutData k)

noncomputable def cutHighCoordinates (s n : ℕ) :
    coefficientModule k (Fin S.actualCutRank) (C.cutHigh s n) ≃ₗ[k] (S.HighStageExponent s n →₀ k) :=
  (C.cutCoefficientEquiv ↥(S.towerHighIdeal k s n)).trans (S.truncCoordinates k s n)

noncomputable def cutHighDegree (s n p : ℕ) :
    Submodule k (coefficientModule k (Fin S.actualCutRank) (C.cutHigh s n)) :=
  (S.towerStageDegree k s p).comap
    (((S.towerHighIdeal k s n).restrictScalars k).subtype.comp
      (C.cutCoefficientEquiv ↥(S.towerHighIdeal k s n)).toLinearMap)

theorem cutHighDegree_mem (s n p : ℕ)
    (a : coefficientModule k (Fin S.actualCutRank) (C.cutHigh s n)) :
    a ∈ C.cutHighDegree s n p ↔ a.val ∈ S.towerStageDegree k s p := Iff.rfl

theorem cutHighDegree_coordinates (s n p : ℕ)
    (a : coefficientModule k (Fin S.actualCutRank) (C.cutHigh s n)) :
    a ∈ C.cutHighDegree s n p ↔ ∀ h : S.HighStageExponent s n,
      S.order h.val.val.val.val ≠ p → C.cutHighCoordinates s n a h=0 :=
  S.truncDegree_coordinates k s n p (C.cutCoefficientEquiv ↥(S.towerHighIdeal k s n) a)

theorem cutHighDegree_variable (s n p : ℕ) (i : Fin S.actualCutRank)
    (a : coefficientModule k (Fin S.actualCutRank) (C.cutHigh s n))
    (ha : a ∈ C.cutHighDegree s n p) :
    (MvPolynomial.X i : S.CutPolynomialRing k) • a ∈ C.cutHighDegree s n (p+1) := by
  rw [C.cutHighDegree_mem] at ha ⊢
  obtain ⟨b,hb,he⟩ := ha
  refine ⟨(C.forms i).val*b,?_,?_⟩
  · change (C.forms i).val*b ∈ S.headDegree k (p+1)
    simpa only [Nat.add_comm 1 p] using S.headDegree_mul_mem k (C.forms i).property hb
  · change Ideal.Quotient.mk (S.jumpIdeal k (s-1)) ((C.forms i).val*b)=_
    change Ideal.Quotient.mk (S.jumpIdeal k (s-1)) b=a.val at he
    rw [map_mul,he]
    exact (C.cutHigh_X_smul s n i (show C.cutHigh s n from a)).symm

/-- The literal Run14 truncation with the action of the same fixed cut. -/
noncomputable def cutHighGrading (s n : ℕ) :
    GradedPolynomialModule k (Fin S.actualCutRank) (C.cutHigh s n) :=
  natCoordinateGrading k (S.HighStageExponent s n) (Fin S.actualCutRank)
    (C.cutHigh s n) (C.cutHighCoordinates s n) (fun h => S.order h.val.val.val.val) (by
      intro i p a ha
      exact (C.cutHighDegree_coordinates s n (p+1) _).mp
        (C.cutHighDegree_variable s n p i a ((C.cutHighDegree_coordinates s n p a).mpr ha)))

theorem cutHighGrading_mem (s n p : ℕ)
    (a : coefficientModule k (Fin S.actualCutRank) (C.cutHigh s n)) :
    a ∈ (C.cutHighGrading s n).degreeSpace p ↔ a.val ∈ S.towerStageDegree k s p := by
  change a ∈ (coordinateDegreeInclusion k (S.HighStageExponent s n)
    (fun h => (S.order h.val.val.val.val : ℤ)) (Fin S.actualCutRank) (C.cutHigh s n)
    (C.cutHighCoordinates s n) p).range ↔ _
  rw [coordinateDegreeInclusion_range]
  simp only [ne_eq,Nat.cast_inj]
  exact (C.cutHighDegree_coordinates s n p a).symm

noncomputable def cutHighDegreeFiberEquiv (s n p : ℕ) (hn : n ≤ p) :
    {h : S.HighStageExponent s n // (S.order h.val.val.val.val : ℤ)=(p:ℤ)} ≃
      S.StageDegreeExponent s p where
  toFun h := ⟨h.val.val,by exact_mod_cast h.property⟩
  invFun h := ⟨⟨h.val,by rw [h.property];exact hn⟩,by exact_mod_cast h.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem cutHighGrading_finrank (s n p : ℕ) (hn : n ≤ p) :
    Module.finrank k ((C.cutHighGrading s n).piece p)=Module.finrank k (S.towerStageDegree k s p) := by
  change Module.finrank k ({h : S.HighStageExponent s n // (S.order h.val.val.val.val : ℤ)=(p:ℤ)} →₀ k)=_
  rw [Module.finrank_finsupp_self,S.towerStageDegree_finrank,
    Fintype.card_congr (cutHighDegreeFiberEquiv (S:=S) s n p hn)]

theorem cutHighGrading_vanish (s n p : ℕ) (hp : S.headTopDegree < p) :
    CategoryTheory.Limits.IsZero ((C.cutHighGrading s n).piece p) := by
  let : IsEmpty {h : S.HighStageExponent s n // (S.order h.val.val.val.val : ℤ)=(p:ℤ)} :=
    ⟨fun h => by
      have ht := S.head_order_le_top h.val.val.val
      have he : S.order h.val.val.val.val=p := by exact_mod_cast h.property
      omega⟩
  change CategoryTheory.Limits.IsZero
    (ModuleCat.of k ({h : S.HighStageExponent s n // (S.order h.val.val.val.val : ℤ)=(p:ℤ)} →₀ k))
  exact ModuleCat.isZero_of_subsingleton _

/-- The bottom piece of this actual grading generates this exact cut module. -/
theorem cutHighGrading_generated (s n : ℕ) (hn : 1 ≤ n) :
    Submodule.span (S.CutPolynomialRing k)
      (Set.range (fun a : (C.cutHighGrading s n).piece (n:ℤ) =>
        (show C.cutHigh s n from (C.cutHighGrading s n).inclusion (n:ℤ) a)))=⊤ := by
  have hle : C.generatorSpace s n ≤ Submodule.span (S.CutPolynomialRing k)
      (Set.range (fun a : (C.cutHighGrading s n).piece (n:ℤ) =>
        (show C.cutHigh s n from (C.cutHighGrading s n).inclusion (n:ℤ) a))) := by
    apply Submodule.span_le.mpr
    rintro a ⟨b,rfl⟩
    have ha : C.degreeHigh s n n le_rfl b ∈ (C.cutHighGrading s n).degreeSpace (n:ℤ) := by
      apply (C.cutHighGrading_mem s n n _).mpr
      exact ⟨b.val,b.property,rfl⟩
    obtain ⟨c,hc⟩ := ha
    exact Submodule.subset_span ⟨c,hc⟩
  rw [C.cutHigh_generated s n hn] at hle
  exact le_antisymm le_top hle
end NSP14.NumericalSemigroup.LinearCutData
