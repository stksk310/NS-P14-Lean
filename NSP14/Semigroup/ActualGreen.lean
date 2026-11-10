module

public import NSP14.Semigroup.QuadraticProduct
public import NSP14.Semigroup.ActualCutRank

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [Field k]

/-- A single prefix ideal of actual independent degree-one forms. -/
noncomputable def linearCutIdeal {n : ℕ} (c : Fin n → S.headDegree k 1) (s : ℕ) : Ideal (S.HeadAlgebra k) :=
  Ideal.span {a | ∃ i : Fin n, i.val < s ∧ a = (c i).val}

noncomputable def linearCutDegree {n : ℕ} (c : Fin n → S.headDegree k 1) (s d : ℕ) :
    Submodule k (S.HeadAlgebra k ⧸ S.linearCutIdeal k c s) :=
  (S.headDegree k d).map (Ideal.Quotient.mkₐ k (S.linearCutIdeal k c s)).toLinearMap

theorem flagSpan_mem_cutIdeal {n : ℕ} (c : Fin n → S.headDegree k 1) (s : ℕ)
    (a : S.headDegree k 1) (ha : a ∈ NSP14.Green.flagSpan (k := k) c s) :
    a.val ∈ S.linearCutIdeal k c s := by
  have hle : NSP14.Green.flagSpan (k := k) c s ≤
      ((S.linearCutIdeal k c s).restrictScalars k).comap (S.headDegree k 1).subtype := by
    apply Submodule.span_le.mpr
    rintro b ⟨i,hi,rfl⟩
    exact Ideal.subset_span ⟨i,hi,rfl⟩
  exact hle ha

theorem quadraticCutImage_mem_cutIdeal {n : ℕ} (c : Fin n → S.headDegree k 1) (s : ℕ)
    (a : S.headDegree k 2)
    (ha : a ∈ NSP14.Green.cutImage (S.quadraticProduct k) (NSP14.Green.flagSpan (k := k) c s)) :
    a.val ∈ S.linearCutIdeal k c s := by
  have hle : NSP14.Green.cutImage (S.quadraticProduct k) (NSP14.Green.flagSpan (k := k) c s) ≤
      ((S.linearCutIdeal k c s).restrictScalars k).comap (S.headDegree k 2).subtype := by
    apply Submodule.span_le.mpr
    rintro b ⟨x,hx,y,rfl⟩
    exact (S.linearCutIdeal k c s).mul_mem_right y.val (S.flagSpan_mem_cutIdeal k c s x hx)
  exact hle ha

noncomputable def linearCutPieceMap {n : ℕ} (c : Fin n → S.headDegree k 1) (s : ℕ) :
    S.headDegree k 2 →ₗ[k] S.linearCutDegree k c s 2 where
  toFun a := ⟨Ideal.Quotient.mk _ a.val, a.val, a.property, rfl⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' r a := Subtype.ext ((Ideal.Quotient.mkₐ k (S.linearCutIdeal k c s)).toLinearMap.map_smul r a.val)

noncomputable def quadraticCutToActual {n : ℕ} (c : Fin n → S.headDegree k 1) (s : ℕ) :
    ((S.headDegree k 2) ⧸ NSP14.Green.cutImage (S.quadraticProduct k) (NSP14.Green.flagSpan (k := k) c s)) →ₗ[k]
      S.linearCutDegree k c s 2 :=
  (NSP14.Green.cutImage (S.quadraticProduct k) (NSP14.Green.flagSpan (k := k) c s)).liftQ
    (S.linearCutPieceMap k c s) (by
      intro a ha
      apply Subtype.ext
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (S.quadraticCutImage_mem_cutIdeal k c s a ha))

theorem quadraticCutToActual_surjective {n : ℕ} (c : Fin n → S.headDegree k 1) (s : ℕ) :
    Function.Surjective (S.quadraticCutToActual k c s) := by
  intro a
  obtain ⟨b,hb,he⟩ := a.property
  refine ⟨Submodule.Quotient.mk (⟨b,hb⟩ : S.headDegree k 2), ?_⟩
  exact Subtype.ext he

/-- Green's full degree-two flag bound for actual A, over any infinite field. -/
theorem actual_green_flag [Infinite k] :
    let a := (S.degreeSet 2).card
    let p := NSP14.Ordinary.quadraticIndex a
    ∃ c : Fin p → S.headDegree k 1, LinearIndependent k c ∧
      ∀ s, s ≤ p → Module.finrank k (S.linearCutDegree k c s 2) ≤
        (p + 1 - s).choose 2 + (a - NSP14.Ordinary.quadraticTriangular p - s) := by
  dsimp only
  let a := (S.degreeSet 2).card
  let p := NSP14.Ordinary.quadraticIndex a
  have hdim : p ≤ Module.finrank k (S.headDegree k 1) := by
    rw [S.headDegree_one_finrank]
    apply NSP14.Ordinary.quadraticIndex_le_of_bound
    unfold NSP14.Ordinary.quadraticTriangular
    rw [Nat.sub_add_cancel (show 1 ≤ S.embeddingDimension from S.embeddingDimension_pos)]
    exact S.degree_two_card_le_quadratic
  have hcap : Module.finrank k (S.headDegree k 2) ≤
      (p + 1).choose 2 + (a - NSP14.Ordinary.quadraticTriangular p) := by
    rw [S.headDegree_two_finrank]
    have h := NSP14.Ordinary.quadraticIndex_lower a
    change a ≤ NSP14.Ordinary.quadraticTriangular p + (a - NSP14.Ordinary.quadraticTriangular p)
    omega
  obtain ⟨c,hc,hs⟩ := NSP14.Green.exists_hyperplane_flag (S.quadraticProduct k)
    (S.quadraticProduct_symmetric k) (S.quadraticProduct_spans k) p
    (a - NSP14.Ordinary.quadraticTriangular p) hdim hcap
  refine ⟨c,hc,?_⟩
  intro s hsp
  exact (LinearMap.finrank_le_finrank_of_surjective (S.quadraticCutToActual_surjective k c s)).trans (hs s hsp)

end NSP14.NumericalSemigroup
