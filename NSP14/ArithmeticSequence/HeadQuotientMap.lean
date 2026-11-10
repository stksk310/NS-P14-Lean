module
public import NSP14.ArithmeticSequence.HeadMultiplication
public import NSP14.Semigroup.AlgebraHeadQuotient
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.NumericalSemigroup
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data) (k : Type) [Field k]

theorem headMonomial_mul (x y : D.source.carrier) :
    D.source.headMonomial k x*D.source.headMonomial k y=D.source.headMonomial k (x+y) := by
  by_cases he : D.source.order (x.val+y.val)=D.source.order x.val+D.source.order y.val
  · exact D.source.headMonomial_mul_live k x y he
  · have hlt : D.source.order x.val+D.source.order y.val<D.source.order (x.val+y.val) :=
      lt_of_le_of_ne (D.source.order_add x.property y.property) (Ne.symm he)
    rw [D.source.headMonomial_mul_dead k x y hlt]
    symm
    apply D.source.headMonomial_zero_of_not_head
    intro hh
    exact he (D.order_add_of_sum_apery x.property y.property ((D.head_iff_apery _).mp hh))

noncomputable def headMonoid : Multiplicative D.source.carrier →* D.source.HeadAlgebra k where
  toFun x := D.source.headMonomial k x.toAdd
  map_one' := by
    change Ideal.Quotient.mk (D.source.xIdeal k) (D.source.initialMonomial k 0)=1
    rw [D.source.initialMonomial_zero,map_one]
  map_mul' x y := (D.headMonomial_mul k x.toAdd y.toAdd).symm

noncomputable def semigroupToHead : D.source.SemigroupRing k →ₐ[k] D.source.HeadAlgebra k :=
  AddMonoidAlgebra.lift k (D.source.HeadAlgebra k) D.source.carrier (D.headMonoid k)

theorem semigroupToHead_single (x : D.source.carrier) (c : k) :
    D.semigroupToHead k (AddMonoidAlgebra.single x c)=c • D.source.headMonomial k x :=
  AddMonoidAlgebra.lift_single _ _ _

theorem semigroupToHead_coordinates (a : D.source.SemigroupRing k) (y : D.source.HeadExponent) :
    D.source.headQuotientEquiv k (D.semigroupToHead k a) y=a.coeff y.val := by
  induction a using AddMonoidAlgebra.induction_on with
  | of x =>
    change D.source.headQuotientEquiv k (D.semigroupToHead k (AddMonoidAlgebra.single x 1)) y=_
    rw [D.semigroupToHead_single,one_smul,D.source.headMonomial_coordinates]
    rfl
  | add a b ha hb => simp only [map_add,Finsupp.add_apply,ha,hb,AddMonoidAlgebra.coeff_add]
  | smul c a ha => simp only [map_smul,Finsupp.smul_apply,ha,AddMonoidAlgebra.coeff_smul]

theorem semigroupToHead_surjective : Function.Surjective (D.semigroupToHead k) := by
  intro a
  let f := (D.source.headQuotientEquiv k a).extendDomain
  refine ⟨(AddMonoidAlgebra.coeffLinearEquiv k).symm f,?_⟩
  apply (D.source.headQuotientEquiv k).injective
  ext y
  rw [D.semigroupToHead_coordinates]
  change f y.val=_
  simp only [f,Finsupp.extendDomain_apply,dite_eq_left y.property]
  rfl

theorem semigroupToHead_ker : RingHom.ker (D.semigroupToHead k)=D.source.semigroupXIdeal k := by
  ext a
  rw [RingHom.mem_ker,D.source.mem_semigroupXIdeal]
  constructor
  · intro h x
    have he := congrArg (fun z => D.source.headQuotientEquiv k z
      ⟨x.val,(D.head_iff_apery _).mpr x.property⟩) h
    simpa only [D.semigroupToHead_coordinates,map_zero,Finsupp.zero_apply] using he
  · intro h
    apply (D.source.headQuotientEquiv k).injective
    ext y
    rw [D.semigroupToHead_coordinates,map_zero,Finsupp.zero_apply]
    exact h ⟨y.val,(D.head_iff_apery _).mp y.property⟩
end NSP14.ArithmeticSequence.Data
