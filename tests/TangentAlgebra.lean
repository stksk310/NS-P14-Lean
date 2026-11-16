module

import NSP14

noncomputable section

open NSP14 NSP14.NumericalSemigroup
open scoped BigOperators DirectSum

section Interfaces
variable (S : NumericalSemigroup) (k : Type*) [Field k]
example : CommRing (S.TangentAlgebra k) := inferInstance
example : Algebra k (S.TangentAlgebra k) := inferInstance
example : S.TangentAlgebra k ≃ₗ[k] (S.carrier →₀ k) := S.tangentCoordinates k
example : (S.xMultiply k).ker ≃ₗ[k] (S.TerminalExponent →₀ k) := S.xKernelEquiv k
example : S.HeadAlgebra k ≃ₗ[k] (S.HeadExponent →₀ k) := S.headQuotientEquiv k
example : CommRing (S.HeadAlgebra k) := inferInstance
example (a b c : S.TangentAlgebra k) : (a*b)*c = a*(b*c) := mul_assoc a b c
example (a : S.TangentAlgebra k) : 1*a=a ∧ a*1=a := ⟨one_mul a, mul_one a⟩
example (r : k) (a b : S.TangentAlgebra k) : (r • a)*b = r • (a*b) := smul_mul_assoc r a b
example (a : S.TangentAlgebra k) : S.tangentCoordinates k (S.xMultiply k a) =
    S.coordinateShift k (S.tangentCoordinates k a) := S.xMultiply_coordinates k a
end Interfaces

namespace TangentExamples

def naturals : NumericalSemigroup where
  carrier := ⊤
  conductor := 0
  cofinite _ _ := by trivial

theorem naturals_m : naturals.multiplicity = 1 :=
  naturals.multiplicity_eq (by decide) (by trivial) (by intro x _ hx; omega)

theorem naturals_order (x : ℕ) : naturals.order x = x := by
  have hlen : naturals.HasLength x x :=
    ⟨fun _ => 1, fun _ => ⟨by trivial, by norm_num⟩, by simp⟩
  have hlo := naturals.length_le_order hlen
  have hhi := naturals.order_bound (show x ∈ naturals from by trivial)
  rw [naturals_m, mul_one] at hhi
  omega

example : (naturals.xMultiply ℚ).ker = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  have hzero : naturals.tangentCoordinates ℚ a = 0 := by
    ext x
    have h := (naturals.coordinateShift_eq_zero ℚ _).1
      ((naturals.mem_xKernel_coordinates ℚ a).1 ha)
    apply h x
    simp [LiveExponent, naturals_order, naturals_m]
  exact (naturals.tangentCoordinates ℚ).injective (by simpa using hzero)

/-- <4,5,11>, expressed as its explicit cofinite set. -/
def singular : NumericalSemigroup where
  carrier :=
    { carrier := {n | n=0 ∨ n=4 ∨ n=5 ∨ n=8 ∨ n=9 ∨ n=10 ∨ 11≤n}
      zero_mem' := Or.inl rfl
      add_mem' := by
        intro x y hx hy
        change x+y=0 ∨ x+y=4 ∨ x+y=5 ∨ x+y=8 ∨ x+y=9 ∨ x+y=10 ∨ 11≤x+y
        change x=0 ∨ x=4 ∨ x=5 ∨ x=8 ∨ x=9 ∨ x=10 ∨ 11≤x at hx
        change y=0 ∨ y=4 ∨ y=5 ∨ y=8 ∨ y=9 ∨ y=10 ∨ 11≤y at hy
        omega }
  conductor := 11
  cofinite _ hn := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hn)))))

theorem singular_m : singular.multiplicity = 4 := by
  apply singular.multiplicity_eq (by decide)
    (show 4 ∈ singular from Or.inr (Or.inl rfl))
  intro x hx hp
  change x=0 ∨ x=4 ∨ x=5 ∨ x=8 ∨ x=9 ∨ x=10 ∨ 11≤x at hx
  omega

def a : singular.carrier := ⟨4, Or.inr (Or.inl rfl)⟩
def t : singular.carrier := ⟨11, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))⟩
def h : singular.carrier := ⟨15, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))⟩

theorem atom_eleven : singular.IsAtom 11 := by
  refine ⟨t.property, by decide, ?_⟩
  intro u hu v hv heq
  change u=0 ∨ u=4 ∨ u=5 ∨ u=8 ∨ u=9 ∨ u=10 ∨ 11≤u at hu
  change v=0 ∨ v=4 ∨ v=5 ∨ v=8 ∨ v=9 ∨ v=10 ∨ 11≤v at hv
  omega

theorem singular_order_eleven : singular.order 11 = 1 := singular.atom_order atom_eleven

theorem singular_order_fifteen : singular.order 15 = 3 := by
  have hlen : singular.HasLength 15 3 :=
    ⟨fun _ => 5, fun _ => ⟨Or.inr (Or.inr (Or.inl rfl)), by norm_num⟩, by norm_num⟩
  have hlo := singular.length_le_order hlen
  have hhi := singular.order_bound h.property
  change singular.order 15 * singular.multiplicity ≤ 15 at hhi
  rw [singular_m] at hhi
  omega

theorem eleven_terminal : singular.Terminal 11 := by
  refine ⟨t.property, ?_⟩
  rw [singular_m, singular_order_eleven]
  change 1+1 < singular.order 15
  rw [singular_order_fifteen]
  decide

theorem fifteen_head : singular.NonAperyHead 15 := by
  simpa only [singular_m] using (singular.terminal_iff_head 11).1 eleven_terminal

example : singular.initialMonomial ℚ t ∈ (singular.xMultiply ℚ).ker := by
  change singular.xMultiply ℚ (singular.initialMonomial ℚ t) = 0
  apply singular.xMultiply_initial_dead
  exact (singular.not_live_iff_terminal t).2 eleven_terminal

example : singular.initialMonomial ℚ t ≠ 0 := singular.initialMonomial_ne_zero ℚ t

example : singular.xMultiply ℚ (singular.initialMonomial ℚ t + singular.initialMonomial ℚ a) =
    singular.xMultiply ℚ (singular.initialMonomial ℚ a) := by
  rw [map_add, singular.xMultiply_initial_dead ℚ t
    ((singular.not_live_iff_terminal t).2 eleven_terminal), zero_add]

example : (singular.actualHeadProjection ℚ) (singular.initialMonomial ℚ h) ≠ 0 := by
  intro hz
  have he := congrArg (fun f : singular.HeadExponent →₀ ℚ => f ⟨h, fifteen_head.1⟩) hz
  change singular.tangentCoordinates ℚ (singular.initialMonomial ℚ h) h = 0 at he
  rw [singular.tangentCoordinates_initial] at he
  norm_num at he

example (r s : ℚ) : singular.coordinateShift ℚ
    (Finsupp.single t r + Finsupp.single t s) = 0 := by
  rw [map_add, singular.coordinateShift_single_dead ℚ t r
    ((singular.not_live_iff_terminal t).2 eleven_terminal),
    singular.coordinateShift_single_dead ℚ t s
    ((singular.not_live_iff_terminal t).2 eleven_terminal), zero_add]

end TangentExamples

-- All new declarations, including structure-instance proofs, are audited transitively.
#print axioms NSP14.NumericalSemigroup.pieceAddCommGroup
#print axioms NSP14.NumericalSemigroup.zeroRepresentative
#print axioms NSP14.NumericalSemigroup.homogeneous_mk_eq
#print axioms NSP14.NumericalSemigroup.pieceGOne
#print axioms NSP14.NumericalSemigroup.pieceGMul
#print axioms NSP14.NumericalSemigroup.pieceGCommRing
#print axioms NSP14.NumericalSemigroup.TangentAlgebra
#print axioms NSP14.NumericalSemigroup.tangentCommRing
#print axioms NSP14.NumericalSemigroup.tangent_of_mul
#print axioms NSP14.NumericalSemigroup.degreeSigmaEquiv
#print axioms NSP14.NumericalSemigroup.tangentCoordinates
#print axioms NSP14.NumericalSemigroup.tangentCoordinates_apply
#print axioms NSP14.NumericalSemigroup.initialMonomial
#print axioms NSP14.NumericalSemigroup.tangentCoordinates_initial
#print axioms NSP14.NumericalSemigroup.tangentBasis
#print axioms NSP14.NumericalSemigroup.tangentBasis_eq_initial
#print axioms NSP14.NumericalSemigroup.initialMonomial_ne_zero
#print axioms NSP14.NumericalSemigroup.initialMonomial_mul_eq_zero_iff
#print axioms NSP14.NumericalSemigroup.initialMonomial_mul_live
#print axioms NSP14.NumericalSemigroup.pieceModule
#print axioms NSP14.NumericalSemigroup.scalarClass
#print axioms NSP14.NumericalSemigroup.pieceGAlgebra
#print axioms NSP14.NumericalSemigroup.tangentAlgebraStructure
#print axioms NSP14.NumericalSemigroup.shiftExponent
#print axioms NSP14.NumericalSemigroup.shiftExponent_injective
#print axioms NSP14.NumericalSemigroup.LiveExponent
#print axioms NSP14.NumericalSemigroup.not_live_iff_terminal
#print axioms NSP14.NumericalSemigroup.liveFilter
#print axioms NSP14.NumericalSemigroup.coordinateShift
#print axioms NSP14.NumericalSemigroup.coordinateShift_single_live
#print axioms NSP14.NumericalSemigroup.coordinateShift_single_dead
#print axioms NSP14.NumericalSemigroup.coordinateShift_eq_zero
#print axioms NSP14.NumericalSemigroup.coordinateShift_ker
#print axioms NSP14.NumericalSemigroup.shift_live_not_head
#print axioms NSP14.NumericalSemigroup.not_head_predecessor
#print axioms NSP14.NumericalSemigroup.coordinateShift_range
#print axioms NSP14.NumericalSemigroup.TerminalExponent
#print axioms NSP14.NumericalSemigroup.HeadExponent
#print axioms NSP14.NumericalSemigroup.coordinateKernelEquiv
#print axioms NSP14.NumericalSemigroup.headProjection
#print axioms NSP14.NumericalSemigroup.headProjection_surjective
#print axioms NSP14.NumericalSemigroup.headProjection_ker
#print axioms NSP14.NumericalSemigroup.coordinateHeadQuotientEquiv
#print axioms NSP14.NumericalSemigroup.xElement
#print axioms NSP14.NumericalSemigroup.xMultiply
#print axioms NSP14.NumericalSemigroup.xMultiply_initial_live
#print axioms NSP14.NumericalSemigroup.xMultiply_initial_dead
#print axioms NSP14.NumericalSemigroup.xMultiply_coordinates
#print axioms NSP14.NumericalSemigroup.mem_xKernel_coordinates
#print axioms NSP14.NumericalSemigroup.xKernelCoordinateEquiv
#print axioms NSP14.NumericalSemigroup.xKernelEquiv
#print axioms NSP14.NumericalSemigroup.xKernelBasis
#print axioms NSP14.NumericalSemigroup.xMultiply_range
#print axioms NSP14.NumericalSemigroup.actualHeadProjection
#print axioms NSP14.NumericalSemigroup.actualHeadProjection_surjective
#print axioms NSP14.NumericalSemigroup.actualHeadProjection_ker
#print axioms NSP14.NumericalSemigroup.headCokernelEquiv
#print axioms NSP14.NumericalSemigroup.xIdeal
#print axioms NSP14.NumericalSemigroup.xIdeal_eq_range
#print axioms NSP14.NumericalSemigroup.HeadAlgebra
#print axioms NSP14.NumericalSemigroup.headQuotientEquiv
#print axioms NSP14.NumericalSemigroup.headBasis
#print axioms NSP14.NumericalSemigroup.terminalMonomial
#print axioms NSP14.NumericalSemigroup.xKernelEquiv_terminal
#print axioms NSP14.NumericalSemigroup.xKernelBasis_eq_initial
#print axioms NSP14.NumericalSemigroup.headQuotientEquiv_mk
#print axioms NSP14.NumericalSemigroup.headQuotientEquiv_initial
#print axioms NSP14.NumericalSemigroup.headBasis_eq_initial
#print axioms NSP14.NumericalSemigroup.head_initial_ne_zero
#print axioms NSP14.NumericalSemigroup.xElement_degree_one
#print axioms NSP14.NumericalSemigroup.xMultiply_of
