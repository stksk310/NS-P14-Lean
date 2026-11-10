module
import NSP14
import tests.JumpStrata

open NSP14
open scoped Classical
noncomputable section
namespace NSP14.Run12GlobalBoundaryAudit

private theorem vector_equiv_terminal (S : NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]
    (t : S.TerminalExponent) :
    S.terminalHeadVectorEquiv k (S.terminalMonomial k t) =
      S.nonAperyMonomial k (S.terminalHeadExponentEquiv t) := by
  apply (S.nonAperyIdealEquiv k).injective
  simp [NumericalSemigroup.terminalHeadVectorEquiv,S.xKernelEquiv_terminal,
    S.nonAperyIdealEquiv_initial]

open Run12Fixtures JumpStrataExamples

-- The unrestricted coordinate bijection does not intertwine the actual S0 action.
-- This does not rule out unrelated abstract module isomorphisms.
example (k : Type*) [CommRing k] [Nontrivial k] :
    changing.terminalHeadVectorEquiv k
      ((MvPolynomial.X atom15 : changing.PolynomialRing k) • changing.terminalMonomial k t26) ≠
    (MvPolynomial.X atom15 : changing.PolynomialRing k) •
      changing.terminalHeadVectorEquiv k (changing.terminalMonomial k t26) := by
  have hr : (MvPolynomial.X atom15 : changing.PolynomialRing k) •
      changing.terminalHeadVectorEquiv k (changing.terminalMonomial k t26)=0 := by
    rw [vector_equiv_terminal]
    apply Subtype.ext
    change changing.polynomialToA k (MvPolynomial.X atom15) *
      changing.headMonomial k (changing.shiftExponent v26)=0
    rw [changing.polynomialToA_X]
    apply changing.headMonomial_mul_dead
    change changing.order 15+changing.order (26+changing.multiplicity)<
      changing.order (15+(26+changing.multiplicity))
    rw [changing_m]
    change changing.order 15+changing.order 35<changing.order 50
    rw [order_15,order_35,order_50]
    decide
  intro he
  rw [base_action_live,hr] at he
  have hz := (changing.terminalHeadVectorEquiv k).injective (he.trans (map_zero _).symm)
  exact changing.initialMonomial_ne_zero k v41 (congrArg Subtype.val hz)

#print axioms vector_equiv_terminal
end NSP14.Run12GlobalBoundaryAudit
