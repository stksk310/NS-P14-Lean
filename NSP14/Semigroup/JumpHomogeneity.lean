module

public import NSP14.Semigroup.JumpDegrees

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def tangentGradeProject (p : ℕ) : S.TangentAlgebra k →ₗ[k] S.TangentAlgebra k :=
  (DirectSum.lof k ℕ (S.GradedPiece k) p).comp (DirectSum.component k ℕ (S.GradedPiece k) p)

omit [Nontrivial k] in
theorem tangentGradeProject_coordinates (p : ℕ) (a : S.TangentAlgebra k) (t : S.carrier) :
    S.tangentCoordinates k (S.tangentGradeProject k p a) t =
      if S.order t.val=p then S.tangentCoordinates k a t else 0 := by
  change S.tangentCoordinates k (DirectSum.of (S.GradedPiece k) p (a p)) t = _
  by_cases h : S.order t.val=p
  · subst p
    simp only [S.tangentCoordinates_apply,DirectSum.of_eq_same,ite_true]
  · rw [S.tangentCoordinates_of_ne k p (a p) t h]
    simp [h]

omit [Nontrivial k] in
theorem tangentGradeProject_mem_jumpGSpace (s p : ℕ) (a : S.TangentAlgebra k)
    (ha : a ∈ S.jumpGSpace k s) : S.tangentGradeProject k p a ∈ S.jumpGSpace k s := by
  change S.tangentCoordinates k _ ∈ Finsupp.supported k k _
  rw [Finsupp.mem_supported']
  intro t ht
  rw [S.tangentGradeProject_coordinates]
  have hz : S.tangentCoordinates k a t = 0 := (Finsupp.mem_supported' k _).1 ha t ht
  simp only [hz,ite_self]

theorem tangentGradeProject_mem_kernel (p : ℕ) (a : (S.xMultiply k).ker) :
    S.tangentGradeProject k p a.val ∈ (S.xMultiply k).ker := by
  rw [S.mem_xKernel_coordinates,S.coordinateShift_ker,Finsupp.mem_supported']
  intro t ht
  rw [S.tangentGradeProject_coordinates]
  have ha := (S.mem_xKernel_coordinates k a.val).1 a.property
  rw [S.coordinateShift_ker] at ha
  have hz := (Finsupp.mem_supported' k _).1 ha t ht
  simp only [hz,ite_self]

/-- Every inherited G-component stays in the actual descending S₀-submodule. -/
theorem descendingJump_homogeneous (s p : ℕ) (a : S.descendingJump k s) :
    (⟨S.tangentGradeProject k p a.val.val,S.tangentGradeProject_mem_kernel k p a.val⟩ :
      (S.xMultiply k).ker) ∈ S.descendingJump k s :=
  S.tangentGradeProject_mem_jumpGSpace k s p a.val.val a.property

theorem headGradeProject_mem_jumpASpace (s p : ℕ) (a : S.HeadAlgebra k)
    (ha : a ∈ S.jumpASpace k s) : S.headGradeProject k p a ∈ S.jumpASpace k s := by
  change S.headQuotientEquiv k _ ∈ Finsupp.supported k k _
  rw [Finsupp.mem_supported']
  intro t ht
  rw [S.headGradeProject_coordinates]
  have hz : S.headQuotientEquiv k a t = 0 := (Finsupp.mem_supported' k _).1 ha t ht
  simp only [hz,ite_self]

/-- Every inherited A-component stays in the actual ascending S₀-submodule. -/
theorem ascendingJump_homogeneous (s p : ℕ) (a : S.ascendingJump k s) :
    (⟨S.headGradeProject k p a.val.val,S.headGradeProject_mem_nonAperyIdeal k p a.val.val a.val.property⟩ :
      (S.nonAperyIdeal k).restrictScalars k) ∈ S.ascendingJump k s :=
  S.headGradeProject_mem_jumpASpace k s p a.val.val a.property

/-- The whole actual T is reached at jump 2. -/
theorem descendingJump_two : S.descendingJump k 2 = ⊤ := by
  apply le_antisymm le_top
  intro a _
  rw [S.mem_descendingJump_coordinates]
  intro t ht
  have hb := S.terminal_jump t.property
  omega

/-- The descending filtration vanishes beyond the actual top degree of Q. -/
theorem descendingJump_top_succ : S.descendingJump k (S.qTopDegree+1) = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have he : S.xKernelEquiv k a = 0 := by
    ext t
    exact (S.mem_descendingJump_coordinates k _ a).1 ha t (by
      have hb := S.terminal_jump_upper t.property
      omega)
  exact (S.xKernelEquiv k).injective (he.trans (map_zero _).symm)

/-- The actual N is exhausted at jump ν. -/
theorem ascendingJump_top : S.ascendingJump k S.qTopDegree = ⊤ := by
  apply le_antisymm le_top
  intro a _
  rw [S.mem_ascendingJump_coordinates]
  intro t ht
  have hb := S.terminal_jump_upper t.property
  omega

/-- There is no ascending contribution below the first possible jump. -/
theorem ascendingJump_one : S.ascendingJump k 1 = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have he : S.nTerminalCoordinates k a = 0 := by
    ext t
    exact (S.mem_ascendingJump_coordinates k 1 a).1 ha t (by
      have hb := S.terminal_jump t.property
      omega)
  exact (S.nTerminalCoordinates k).injective (he.trans (map_zero _).symm)

end NSP14.NumericalSemigroup
