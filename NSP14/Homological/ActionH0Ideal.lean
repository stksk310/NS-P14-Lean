module
public import NSP14.Homological.ActionKoszulH0
public import Mathlib.RingTheory.Ideal.Span
@[expose] public section
open CategoryTheory
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R]

noncomputable def actionRegularComplex (rs : List R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  actionKoszul R rs (ModuleCat.of R R)

/-- The native boundary space is the ideal of the actual elements, with
its full R-action, even when the module is infinite over a coefficient field. -/
theorem actionVariableSubmodule_regular (rs : List R) :
    actionVariableSubmodule R rs (ModuleCat.of R R)=Ideal.span {a | a∈rs} := by
  induction rs with
  | nil => simp [actionVariableSubmodule]
  | cons r rs ih =>
    have hs : {a : R | a∈r::rs}=insert r {a | a∈rs} := by ext a;simp
    change (r • 𝟙 (ModuleCat.of R R)).hom.range ⊔ actionVariableSubmodule R rs (ModuleCat.of R R)=_
    rw [ih,hs,Ideal.span_insert]
    congr 1
    ext a
    change (∃ b : R,r*b=a) ↔ a∈Ideal.span {r}
    rw [Ideal.mem_span_singleton']
    simp only [mul_comm]

/-- Zeroth native Koszul homology is the native quotient as an R-module;
all commuting scalar actions are retained by this equivalence. -/
noncomputable def actionRegularH0Equiv (rs : List R) :
    (actionRegularComplex R rs).homology 0 ≃ₗ[R] R ⧸ Ideal.span {a | a∈rs} :=
  (actionH0Equiv R rs (ModuleCat.of R R)).trans
    (Submodule.quotEquivOfEq _ _ (actionVariableSubmodule_regular R rs))
end NSP14.Homological
