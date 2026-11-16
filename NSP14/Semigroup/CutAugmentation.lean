module
public import NSP14.Semigroup.TruncGeneration
public import NSP14.Semigroup.TruncCoordinates
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

theorem form_mul_highSpace (n : ℕ) (c : S.headDegree k 1) (a : S.HeadAlgebra k)
    (ha : a ∈ S.highSpace k n) : c.val*a ∈ S.highSpace k (n+1) := by
  have hs : ∀ h ∈ (S.headQuotientEquiv k a).support,n ≤ S.order h.val.val :=
    (Finsupp.mem_supported k _).1 ha
  rw [← S.head_expansion k a,Finsupp.sum,Finset.mul_sum]
  apply (S.highSpace k (n+1)).sum_mem
  intro h hh
  rw [mul_smul_comm]
  apply (S.highSpace k (n+1)).smul_mem
  have hb : S.headBasis k h ∈ S.headDegree k (S.order h.val.val) := by
    rw [← S.headMonomial_eq_basis k h]
    exact S.headMonomial_mem_degree k h.val _ rfl
  apply S.headDegree_le_highSpace k (n+1) (1+S.order h.val.val) (by have := hs h hh; omega)
  exact S.headDegree_mul_mem k (n:=1) (p:=S.order h.val.val) c.property hb

namespace LinearCutData
variable {S k} (C : S.LinearCutData k)

noncomputable def highInclusion (s n : ℕ) : C.cutHigh s (n+1) →ₗ[S.CutPolynomialRing k] C.cutHigh s n where
  toFun a := ⟨a.val,by
    exact Ideal.map_mono (S.highIdeal_antitone k (Nat.le_succ n)) a.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def variableToNext (s n : ℕ) (i : Fin S.actualCutRank) :
    C.cutHigh s n →ₗ[S.CutPolynomialRing k] C.cutHigh s (n+1) where
  toFun a := ⟨((MvPolynomial.X i : S.CutPolynomialRing k) • a).val,by
    obtain ⟨b,hb,he⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 a.property
    rw [C.cutHigh_X_smul,← he,← map_mul]
    exact Ideal.mem_map_of_mem _ (S.form_mul_highSpace k n (C.forms i) b hb)⟩
  map_add' a b := Subtype.ext (congrArg (fun x : C.cutHigh s n => x.val) (smul_add (MvPolynomial.X i : S.CutPolynomialRing k) a b))
  map_smul' r a := Subtype.ext (congrArg (fun x : C.cutHigh s n => x.val) (smul_comm (MvPolynomial.X i : S.CutPolynomialRing k) r a))

noncomputable def variableEnd (s n : ℕ) (i : Fin S.actualCutRank) :
    C.cutHigh s n →ₗ[S.CutPolynomialRing k] C.cutHigh s n :=
  (C.highInclusion s n).comp (C.variableToNext s n i)

theorem variableEnd_val (s n : ℕ) (i : Fin S.actualCutRank) (a : C.cutHigh s n) :
    (C.variableEnd s n i a).val = Ideal.Quotient.mk _ (C.forms i).val*a.val :=
  C.cutHigh_X_smul s n i a

noncomputable def positiveSpace (s n : ℕ) : Submodule (S.CutPolynomialRing k) (C.cutHigh s n) :=
  ⨆ i : Fin S.actualCutRank, (C.variableEnd s n i).range

/-- The variable multiples are exactly the next-degree truncation. This
identifies the actual bottom quotient with the augmentation quotient. -/
theorem positiveSpace_eq_next (s n : ℕ) (hn : 1 ≤ n) :
    C.positiveSpace s n = (C.highInclusion s n).range := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact LinearMap.range_comp_le_range _ _
  · have hgen : C.generatorSpace s (n+1) ≤ (C.positiveSpace s n).comap (C.highInclusion s n) := by
      apply Submodule.span_le.mpr
      rintro a ⟨v,rfl⟩
      obtain ⟨b,hb⟩ := S.headFormMap_surjective k C n hn v
      have hb' : (∑ i, (C.forms i).val*(b i).val)=v.val := congrArg Subtype.val hb
      have heq : C.highInclusion s n (C.degreeHigh s (n+1) (n+1) le_rfl v) =
          ∑ i, C.variableEnd s n i (C.degreeHigh s n n le_rfl (b i)) := by
        apply Subtype.ext
        rw [C.cutHigh_sum_values]
        simp only [C.variableEnd_val]
        change Ideal.Quotient.mk (S.jumpIdeal k (s-1)) v.val =
          ∑ i, Ideal.Quotient.mk _ (C.forms i).val*Ideal.Quotient.mk _ (b i).val
        rw [← hb',map_sum]
        simp only [map_mul]
      change C.highInclusion s n _ ∈ C.positiveSpace s n
      rw [heq]
      apply (C.positiveSpace s n).sum_mem
      intro i _
      exact (le_iSup (fun i => (C.variableEnd s n i).range) i) ⟨_,rfl⟩
    rw [C.cutHigh_generated s (n+1) (by omega)] at hgen
    rintro a ⟨b,rfl⟩
    exact hgen (Submodule.mem_top : b ∈ ⊤)

end LinearCutData
end NSP14.NumericalSemigroup
