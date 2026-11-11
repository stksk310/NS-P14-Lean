module
public import NSP14.Homological.PolynomialModules
public import NSP14.Homological.Betti
public import NSP14.Semigroup.CompletedComparison
@[expose] public section
namespace NSP14.NumericalSemigroup
variable (S T : NumericalSemigroup) (h : S.carrier=T.carrier)

include h in
/-- The chosen conductor witness does not affect actual order. -/
theorem carrier_order (n : ℕ) : S.order n=T.order n := by
  cases S;cases T;cases h;rfl

noncomputable def carrierExponentEquiv : S.carrier ≃+ T.carrier := by
  cases S;cases T;cases h;exact AddEquiv.refl _

variable (k : Type) [Field k]

noncomputable def carrierPieceEquiv (n : ℕ) : S.GradedPiece k n ≃ₗ[k] T.GradedPiece k n := by
  cases S;cases T;cases h;exact LinearEquiv.refl _ _

/-- The actual graded algebra is independent of the cofinite witness;
this is not an isomorphism to a different normalized numerical semigroup. -/
noncomputable def carrierTangentEquiv : S.TangentAlgebra k ≃ₐ[k] T.TangentAlgebra k := by
  cases S;cases T;cases h;exact AlgEquiv.refl

theorem carrierTangentEquiv_of (n : ℕ) (a : S.GradedPiece k n) :
    S.carrierTangentEquiv T h k (DirectSum.of (S.GradedPiece k) n a)=
      DirectSum.of (T.GradedPiece k) n (S.carrierPieceEquiv T h k n a) := by
  cases S;cases T;cases h;rfl

theorem carrierTangentEquiv_initial (a : S.carrier) :
    S.carrierTangentEquiv T h k (S.initialMonomial k a)=
      T.initialMonomial k (S.carrierExponentEquiv T h a) := by
  cases S;cases T;cases h;rfl

noncomputable def carrierCompletedEquiv : S.FormalTangentAlgebra k ≃ₐ[k] T.FormalTangentAlgebra k :=
  (S.completedGradedAlgEquiv k).symm.trans
    ((S.carrierTangentEquiv T h k).trans (T.completedGradedAlgEquiv k))

include h in
theorem carrier_totalBetti (i : ℕ) :
    NSP14.Homological.totalBetti k S.AtomExponent
      (ModuleCat.of (S.FullPolynomialRing k) (S.TangentAlgebra k)) i=
    NSP14.Homological.totalBetti k T.AtomExponent
      (ModuleCat.of (T.FullPolynomialRing k) (T.TangentAlgebra k)) i := by
  cases S;cases T;cases h;rfl
end NSP14.NumericalSemigroup
