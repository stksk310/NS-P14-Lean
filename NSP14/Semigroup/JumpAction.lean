module

public import NSP14.Semigroup.JumpSlice

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

theorem initial_product_coordinate (g t u : S.carrier) :
    S.tangentCoordinates k (S.initialMonomial k g * S.initialMonomial k t) u =
      if S.order (g.val+t.val)=S.order g.val+S.order t.val then
        Finsupp.single (g+t) (1:k) u else 0 := by
  by_cases hl : S.order (g.val+t.val)=S.order g.val+S.order t.val
  · rw [S.initialMonomial_mul_live k g t hl, S.tangentCoordinates_initial]
    simp [hl]
  · have ho := S.order_add g.property t.property
    rw [(S.initialMonomial_mul_eq_zero_iff k g t).2 (by omega), map_zero]
    simp [hl]

theorem head_product_coordinate (g h : S.carrier) (u : S.HeadExponent) :
    S.headQuotientEquiv k (S.headMonomial k g * S.headMonomial k h) u =
      if S.order (g.val+h.val)=S.order g.val+S.order h.val then
        Finsupp.single (g+h) (1:k) u.val else 0 := by
  by_cases hl : S.order (g.val+h.val)=S.order g.val+S.order h.val
  · rw [S.headMonomial_mul_live k g h hl, S.headMonomial_coordinates]
    simp [hl]
  · have ho := S.order_add g.property h.property
    rw [S.headMonomial_mul_dead k g h (by omega), map_zero]
    simp [hl]

/-- Equal jump at both endpoints gives equality of the actual multiplication matrices. -/
theorem same_jump_product_coordinate (g : S.carrier) (t u : S.TerminalExponent)
    (hj : S.jump t.val.val = S.jump u.val.val) :
    S.tangentCoordinates k (S.initialMonomial k g*S.initialMonomial k t.val) u.val =
      S.headQuotientEquiv k
        (S.headMonomial k g*S.headMonomial k (S.shiftExponent t.val))
        (S.terminalHeadExponentEquiv u).val := by
  rw [S.initial_product_coordinate, S.head_product_coordinate]
  have ht : (S.terminalHeadExponentEquiv u).val.val = S.shiftExponent u.val := rfl
  change (if S.order (g.val+t.val.val)=S.order g.val+S.order t.val.val then
    Finsupp.single (g+t.val) (1:k) u.val else 0) =
    (if S.order (g.val+(t.val.val+S.multiplicity))=S.order g.val+S.order (t.val.val+S.multiplicity) then
      Finsupp.single (g+S.shiftExponent t.val) (1:k) (S.shiftExponent u.val) else 0)
  by_cases he : g+t.val=u.val
  · have hen : g.val+t.val.val=u.val.val := congrArg Subtype.val he
    have hj' : S.jump (t.val.val+g.val)=S.jump t.val.val := by
      rw [Nat.add_comm,hen]
      exact hj.symm
    have hl := S.live_iff_of_equal_jump t.val.property g.property hj'
    have hl' : (S.order (g.val+t.val.val)=S.order g.val+S.order t.val.val) ↔
      (S.order (g.val+(t.val.val+S.multiplicity))=S.order g.val+S.order (t.val.val+S.multiplicity)) := by
      simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hl
    have hes : g+S.shiftExponent t.val=S.shiftExponent u.val := by
      apply Subtype.ext
      change g.val+(t.val.val+S.multiplicity)=u.val.val+S.multiplicity
      omega
    simp [he,hes,hl']
  · have hes : g+S.shiftExponent t.val≠S.shiftExponent u.val := by
      intro h
      apply he
      apply Subtype.ext
      have hh := congrArg Subtype.val h
      change g.val+(t.val.val+S.multiplicity)=u.val.val+S.multiplicity at hh
      change g.val+t.val.val=u.val.val
      omega
    simp [he,hes]

/-- An input with strictly larger jump cannot contribute to a smaller-jump T coordinate. -/
theorem terminal_product_coordinate_zero (g : S.carrier) (t u : S.TerminalExponent)
    (hj : S.jump u.val.val < S.jump t.val.val) :
    S.tangentCoordinates k (S.initialMonomial k g*S.initialMonomial k t.val) u.val = 0 := by
  rw [S.initial_product_coordinate]
  split_ifs with hl
  · have hne : g+t.val≠u.val := by
      intro he
      have hn : g.val+t.val.val=u.val.val := congrArg Subtype.val he
      have hm := S.jump_le_of_live_base t.val.property g.property
        (show S.order (t.val.val+g.val)=S.order t.val.val+S.order g.val by
          simpa only [Nat.add_comm] using hl)
      rw [Nat.add_comm,hn] at hm
      omega
    simp [hne]
  · rfl

/-- An input with strictly smaller jump cannot contribute to a larger-jump N coordinate. -/
theorem head_product_coordinate_zero (g : S.carrier) (t u : S.TerminalExponent)
    (hj : S.jump t.val.val < S.jump u.val.val) :
    S.headQuotientEquiv k
      (S.headMonomial k g*S.headMonomial k (S.shiftExponent t.val))
      (S.terminalHeadExponentEquiv u).val = 0 := by
  rw [S.head_product_coordinate]
  split_ifs with hl
  · have hne : g+S.shiftExponent t.val≠(S.terminalHeadExponentEquiv u).val.val := by
      intro he
      have hn := congrArg Subtype.val he
      change g.val+(t.val.val+S.multiplicity)=u.val.val+S.multiplicity at hn
      have hsum : g.val+t.val.val=u.val.val := by omega
      have hm := S.jump_le_of_live_head t.val.property g.property
        (show S.order (t.val.val+g.val+S.multiplicity)=S.order (t.val.val+S.multiplicity)+S.order g.val by
          change S.order (g.val+(t.val.val+S.multiplicity))=S.order g.val+S.order (t.val.val+S.multiplicity) at hl
          simpa only [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hl)
      rw [Nat.add_comm,hsum] at hm
      omega
    simp [hne]
  · rfl

/-- The matrix comparison extends to every actual G element, hence to every S₀ polynomial. -/
theorem same_jump_action_coordinate (r : S.TangentAlgebra k) (t u : S.TerminalExponent)
    (hj : S.jump t.val.val = S.jump u.val.val) :
    S.tangentCoordinates k (r*S.initialMonomial k t.val) u.val =
      S.headQuotientEquiv k
        (S.toHeadAlgebra k r*S.headMonomial k (S.shiftExponent t.val))
        (S.terminalHeadExponentEquiv u).val := by
  let l : S.TangentAlgebra k →ₗ[k] k :=
    { toFun := fun r => S.tangentCoordinates k (r*S.initialMonomial k t.val) u.val
      map_add' := by intros; simp only [add_mul,map_add,Finsupp.add_apply]
      map_smul' := by intros; simp only [smul_mul_assoc,map_smul,Finsupp.smul_apply,RingHom.id_apply] }
  let q : S.TangentAlgebra k →ₗ[k] k :=
    { toFun := fun r => S.headQuotientEquiv k
        (S.toHeadAlgebra k r*S.headMonomial k (S.shiftExponent t.val)) (S.terminalHeadExponentEquiv u).val
      map_add' := by intros; simp only [map_add,add_mul,Finsupp.add_apply]
      map_smul' := by intros; simp only [map_smul,smul_mul_assoc,Finsupp.smul_apply,RingHom.id_apply] }
  have he : l=q := by
    apply (S.tangentBasis k).ext
    intro g
    change S.tangentCoordinates k (S.tangentBasis k g*S.initialMonomial k t.val) u.val = _
    rw [S.tangentBasis_eq_initial]
    exact S.same_jump_product_coordinate k g t u hj
  exact LinearMap.congr_fun he r

end NSP14.NumericalSemigroup
