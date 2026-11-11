module
public import NSP14.Endpoint.FiberAssembly
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

noncomputable def fiberExponentStep (r : Fin D.u) (i : Fin 2)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r} :=
  ⟨b.val+Finsupp.single i 1,D.coreFiber_upward r b.property
    ⟨by simp only [Finsupp.add_apply];omega,by simp only [Finsupp.add_apply];omega⟩⟩

noncomputable def fiberIndexStep (i : Fin 2) (b : D.FiberBasisIndex) : D.FiberBasisIndex :=
  ⟨b.1,D.fiberExponentStep b.1 i b.2⟩

theorem fiberPolynomialPoint_step (r : Fin D.u) (i : Fin 2)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    D.fiberPolynomialPoint r (D.fiberExponentStep r i b)=
      D.fiberPolynomialPoint r b+D.coreGeneratorPoint (D.endpointVariable i) := by
  have hi : i=0 ∨ i=1 := by
    by_cases h : i.val=0
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by have := i.isLt;omega))
  rcases hi with rfl|rfl
  all_goals
    apply Subtype.ext
    apply Prod.ext
  all_goals
    simp [fiberPolynomialPoint,fiberExponentStep,decodeCoordinate,coreGeneratorPoint,
      endpointVariable,xVariable,vVariable]
  all_goals ring

variable (k : Type) [Field k]

theorem coreFiberBasis_X (r : Fin D.u) (i : Fin 2)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    (MvPolynomial.X i : D.EndpointRing k) • D.coreFiberBasis k r b=
      D.coreFiberBasis k r (D.fiberExponentStep r i b) := by
  apply Subtype.ext
  change (MvPolynomial.X i : D.EndpointRing k)*(D.coreFiberBasis k r b).val=
    (D.coreFiberBasis k r (D.fiberExponentStep r i b)).val
  rw [D.coreFiberBasis_val,D.coreFiberBasis_val,MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  change MvPolynomial.monomial (Finsupp.single i 1+b.val) (1:k)=
    MvPolynomial.monomial (b.val+Finsupp.single i 1) (1:k)
  rw [add_comm]

theorem coreSumBasis_X (i : Fin 2) (b : D.FiberBasisIndex) :
    (MvPolynomial.X i : D.EndpointRing k) • D.coreSumBasis k b=
      D.coreSumBasis k (D.fiberIndexStep i b) := by
  rw [D.coreSumBasis_apply,D.coreSumBasis_apply,← DFinsupp.single_smul,D.coreFiberBasis_X]
  rfl

theorem coreMonomial_mul (p q : D.corePoints) :
    D.coreMonomial k p*D.coreMonomial k q=D.coreMonomial k (p+q) := by
  simp only [coreMonomial,AddMonoidAlgebra.single_mul_single,one_mul]

/-- Compatibility is proved on the actual ideal monomial bases, and
then extended coefficient-linearly; no polynomial-linearity premise is added. -/
theorem coreFiberAssembly_variable (i : Fin 2) (a : ⨁ r : Fin D.u,D.coreFiberIdeal k r) :
    D.coreFiberLinearAssembly k ((MvPolynomial.X i : D.EndpointRing k) • a)=
      D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i))*D.coreFiberLinearAssembly k a := by
  have ha : a∈Submodule.span k (Set.range (D.coreSumBasis k)) := by
    rw [(D.coreSumBasis k).span_eq]
    trivial
  refine Submodule.span_induction (p:=fun a _ =>
    D.coreFiberLinearAssembly k ((MvPolynomial.X i : D.EndpointRing k) • a)=
      D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i))*D.coreFiberLinearAssembly k a) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨b,rfl⟩
    rw [D.coreSumBasis_X,D.coreFiberLinearAssembly_basis,D.coreFiberLinearAssembly_basis,
      D.coreMonomial_mul]
    change D.coreMonomial k (D.fiberPolynomialPoint b.1 (D.fiberExponentStep b.1 i b.2))=_
    rw [D.fiberPolynomialPoint_step,add_comm]
  · simp only [smul_zero,map_zero,mul_zero]
  · intro a b _ _ ha hb
    simp only [smul_add,map_add,mul_add,ha,hb]
  · intro c a _ ha
    rw [smul_comm (MvPolynomial.X i : D.EndpointRing k) c a,map_smul,ha,map_smul,mul_smul_comm]
end NSP14.Endpoint.Data
