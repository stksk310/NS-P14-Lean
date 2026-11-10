module
public import NSP14.Homological.MinorRank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
@[expose] public section
namespace NSP14.Homological
variable (k : Type*) [Field k] {I X Y : Type*} [Fintype I] [DecidableEq I]
  [AddCommGroup X] [Module k X] [AddCommGroup Y] [Module k Y]

/-- A minor of actual source vectors and actual target linear functionals
bounds the rank of an actual linear map. Only target/range finiteness is
needed; no finite dimension of the source is silently assumed. -/
theorem functional_minor_rank_lower_bound [Module.Finite k Y]
    (d : X →ₗ[k] Y) (columns : I → X) (rows : I → Y →ₗ[k] k)
    (hdet : Matrix.det (fun i j => rows i (d (columns j))) ≠ 0) :
    Fintype.card I ≤ Module.finrank k d.range := by
  let v : I → d.range := fun j => ⟨d (columns j),⟨columns j,rfl⟩⟩
  let F : d.range →ₗ[k] (I → k) :=
    { toFun y i := rows i y.val
      map_add' a b := by ext i;exact (rows i).map_add _ _
      map_smul' c a := by ext i;exact (rows i).map_smul _ _ }
  have hli : LinearIndependent k (fun i => F (v i)) :=
    Matrix.linearIndependent_cols_of_det_ne_zero hdet
  have hv := LinearIndependent.of_comp F hli
  exact hv.fintype_card_le_finrank

theorem triangular_functional_minor_rank_lower_bound [Module.Finite k Y] [LinearOrder I]
    (d : X →ₗ[k] Y) (columns : I → X) (rows : I → Y →ₗ[k] k)
    (htri : Matrix.IsUpperTriangular (fun i j => rows i (d (columns j))))
    (hdiag : ∀ i,rows i (d (columns i))=1 ∨ rows i (d (columns i)) = -1) :
    Fintype.card I ≤ Module.finrank k d.range := by
  apply functional_minor_rank_lower_bound k d columns rows
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  rcases hdiag i with h|h <;> simp [h]
end NSP14.Homological
