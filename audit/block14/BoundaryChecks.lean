module

import NSP14
import Mathlib.Algebra.Field.ZMod

open NSP14 NSP14.NumericalSemigroup NSP14.Green

namespace Run14IndependentAudit

instance : Fact (Nat.Prime 2) := ⟨by decide⟩

-- The nonzero-point avoidance lemma really needs an infinite field.
theorem finite_field_avoidance_fails :
    ¬ ∃ t : ZMod 2, t ≠ 0 ∧ (1+t) ≠ 0 := by decide

abbrev L := NSP14.Homological.InfiniteScalarField (ZMod 2)
abbrev V := L × L

noncomputable def alternatingProduct : V →ₗ[L] V →ₗ[L] L where
  toFun x :=
    { toFun := fun y => x.1*y.2+x.2*y.1
      map_add' := by intro y z; simp only [Prod.fst_add,Prod.snd_add]; ring
      map_smul' := by
        intro c y
        change x.1*(c*y.2)+x.2*(c*y.1)=c*(x.1*y.2+x.2*y.1)
        ring }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change (x.1+y.1)*z.2+(x.2+y.2)*z.1 = _
    change _ = (x.1*z.2+x.2*z.1)+(y.1*z.2+y.2*z.1)
    ring
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    change (c*x.1)*y.2+(c*x.2)*y.1 = c*(x.1*y.2+x.2*y.1)
    ring

theorem alternating_symmetric (x y : V) : alternatingProduct x y = alternatingProduct y x := by
  change x.1*y.2+x.2*y.1=y.1*x.2+y.2*x.1
  ring

theorem all_squares_zero (x : V) : alternatingProduct x x = 0 := by
  let : CharP L 2 := NSP14.Homological.infiniteScalarField_charP (ZMod 2) 2
  have h2 : (2:L)=0 := CharP.cast_eq_zero L 2
  change x.1*x.2+x.2*x.1=0
  calc
    _ = (2:L)*(x.1*x.2) := by ring
    _ = 0 := by rw [h2,zero_mul]

theorem alternating_nonzero : alternatingProduct (1,0) (0,1)=1 := by
  change (1:L)*1+0*0=1
  ring

theorem alternating_spans : bilinearSpan alternatingProduct = ⊤ := by
  have h1 : (1:L) ∈ bilinearSpan alternatingProduct :=
    Submodule.subset_span ⟨(1,0),(0,1),alternating_nonzero⟩
  apply top_unique
  intro z _
  simpa using (bilinearSpan alternatingProduct).smul_mem z h1

-- Exercise Green's genuinely alternating, nonzero characteristic-two branch.
theorem alternating_one_cut :
    ∃ c : Fin 1 → V, LinearIndependent L c ∧
      cutImage alternatingProduct (flagSpan (k := L) c 1)=⊤ := by
  apply exists_quadratic_zero_cut alternatingProduct alternating_symmetric alternating_spans 1 0
  · decide
  · simp [Module.finrank_prod]
  · simp

-- The offset threshold is exact, not just an eventual loose bound.
theorem stabilization_iff (S : NumericalSemigroup) (r : Fin S.multiplicity) (q : ℕ) :
    S.order (S.apery r+q*S.multiplicity)=S.offsetLevel r+q ↔
      S.leastOffsetLength r ≤ S.offsetLevel r+q := by
  constructor
  · intro he
    have h := S.order_length (S.apery_add_multiple r q)
    rw [he] at h
    apply S.leastOffsetLength_le r
    convert h using 1
    rw [S.apery_eq_offset r]
    ring
  · exact S.order_stabilization r q

#print axioms finite_field_avoidance_fails
#print axioms alternatingProduct
#print axioms alternating_symmetric
#print axioms all_squares_zero
#print axioms alternating_nonzero
#print axioms alternating_spans
#print axioms alternating_one_cut
#print axioms stabilization_iff

end Run14IndependentAudit
