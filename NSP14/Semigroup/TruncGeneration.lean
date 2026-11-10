module
public import NSP14.Semigroup.TowerExact
public import NSP14.Semigroup.CutGeneration
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable {S : NumericalSemigroup} {k : Type} [Field k]
namespace LinearCutData
variable (C : S.LinearCutData k)

noncomputable def cutHigh (s n : ℕ) : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) ↥(S.towerHighIdeal k s n))
noncomputable def cutStage (s : ℕ) : ModuleCat (S.CutPolynomialRing k) :=
  C.restrictFunctor.obj (ModuleCat.of (S.PolynomialRing k) (S.TowerStage k s))

noncomputable def cutHighVal (s n : ℕ) : C.cutHigh s n →+ S.TowerStage k s where
  toFun a := a.val
  map_zero' := rfl
  map_add' _ _ := rfl

theorem cutHigh_sum_values {ι : Type*} (s n : ℕ) (u : Finset ι) (f : ι → C.cutHigh s n) :
    (∑ i ∈ u,f i).val = ∑ i ∈ u,(f i).val :=
  map_sum (C.cutHighVal s n) f u

noncomputable def degreeHigh (s n d : ℕ) (hd : n ≤ d) (a : S.headDegree k d) : C.cutHigh s n :=
  ⟨Ideal.Quotient.mk _ a.val,Ideal.mem_map_of_mem _ (S.headDegree_le_highSpace k n d hd a.property)⟩

theorem cutHigh_X_smul (s n : ℕ) (i : Fin S.actualCutRank) (a : C.cutHigh s n) :
    ((MvPolynomial.X i : S.CutPolynomialRing k) • a).val =
      Ideal.Quotient.mk _ (C.forms i).val * a.val := by
  change S.polynomialToA k (C.toPolynomialRing (MvPolynomial.X i)) • a.val = _
  rw [C.toPolynomialRing_X,C.polynomialForm_image]
  rfl

noncomputable def generatorSpace (s n : ℕ) : Submodule (S.CutPolynomialRing k) (C.cutHigh s n) :=
  Submodule.span (S.CutPolynomialRing k) (Set.range (C.degreeHigh s n n le_rfl))

theorem degreeHigh_mem_generators (s n d : ℕ) (hn : 1 ≤ n) (hd : n ≤ d)
    (a : S.headDegree k d) : C.degreeHigh s n d hd a ∈ C.generatorSpace s n := by
  induction d using Nat.strong_induction_on with
  | ind d ih =>
    by_cases he : d=n
    · subst d
      exact Submodule.subset_span ⟨a,rfl⟩
    · have hdn : n ≤ d-1 := by omega
      have hd1 : 1 ≤ d-1 := by omega
      obtain ⟨b,hb⟩ := S.headFormMap_surjective k C (d-1) hd1
        ⟨a.val,by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ d)] using a.property⟩
      have hb' : (∑ i, (C.forms i).val*(b i).val)=a.val := congrArg Subtype.val hb
      have heq : C.degreeHigh s n d hd a = ∑ i, (MvPolynomial.X i : S.CutPolynomialRing k) •
          C.degreeHigh s n (d-1) hdn (b i) := by
        apply Subtype.ext
        change Ideal.Quotient.mk _ a.val = _
        rw [C.cutHigh_sum_values]
        simp only [C.cutHigh_X_smul]
        change Ideal.Quotient.mk _ a.val = ∑ i, Ideal.Quotient.mk _ (C.forms i).val*Ideal.Quotient.mk _ (b i).val
        rw [← hb',map_sum]
        simp only [map_mul]
      rw [heq]
      apply (C.generatorSpace s n).sum_mem
      intro i _
      exact (C.generatorSpace s n).smul_mem _ (ih (d-1) (by omega) hdn (b i))

/-- Actual truncations are generated over this same P in their bottom degree. -/
theorem cutHigh_generated (s n : ℕ) (hn : 1 ≤ n) : C.generatorSpace s n = ⊤ := by
  apply top_unique
  intro a _
  obtain ⟨b,hb,he⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 a.property
  have hs : ∀ h ∈ (S.headQuotientEquiv k b).support,n ≤ S.order h.val.val :=
    (Finsupp.mem_supported k _).1 hb
  have heq : a = ∑ h : ↥(S.headQuotientEquiv k b).support,
      (MvPolynomial.C (S.headQuotientEquiv k b h.val) : S.CutPolynomialRing k) •
      C.degreeHigh s n (S.order h.val.val.val) (hs h.val h.property)
        ⟨S.headBasis k h.val,by rw [← S.headMonomial_eq_basis k h.val]; exact S.headMonomial_mem_degree k h.val.val _ rfl⟩ := by
    apply Subtype.ext
    conv_lhs => rw [← he,← S.head_expansion k b,Finsupp.sum,map_sum]
    rw [C.cutHigh_sum_values]
    rw [← Finset.sum_coe_sort (S.headQuotientEquiv k b).support
      (fun h => Ideal.Quotient.mk (S.jumpIdeal k (s-1)) ((S.headQuotientEquiv k b h) • S.headBasis k h))]
    apply Finset.sum_congr rfl
    intro h _
    change Ideal.Quotient.mk (S.jumpIdeal k (s-1)) ((S.headQuotientEquiv k b h.val) • S.headBasis k h.val) =
      S.polynomialToA k (C.toPolynomialRing (MvPolynomial.C (S.headQuotientEquiv k b h.val))) •
        Ideal.Quotient.mk (S.jumpIdeal k (s-1)) (S.headBasis k h.val)
    simp only [MvPolynomial.algHom_C,AlgHom.commutes,algebraMap_smul]
    exact (Ideal.Quotient.mkₐ k (S.jumpIdeal k (s-1))).toLinearMap.map_smul _ _
  rw [heq]
  apply (C.generatorSpace s n).sum_mem
  intro h _
  exact (C.generatorSpace s n).smul_mem _ (C.degreeHigh_mem_generators s n _ hn (hs h.val h.property) _)

end LinearCutData
end NSP14.NumericalSemigroup
