module

public import NSP14
public import tests.Run12Fixtures
public import tests.Run12BasicExamples

@[expose] public section

noncomputable section
open NSP14 NSP14.NumericalSemigroup
open scoped Classical

section Generic
variable (S : NumericalSemigroup) (k : Type*) [CommRing k]
example : S.TangentAlgebra k ≃ₐ[k] S.FormalTangentAlgebra k := S.completedGradedAlgEquiv k
example (n : ℕ) (f : S.FormalSemigroupRing k) :
    f ∈ S.formalMaximalIdeal k ^ n ↔ ∀ x : S.carrier, S.order x.val<n → PowerSeries.coeff x.val f.val=0 :=
  S.mem_formalMaximalIdeal_pow k n f
example (n : ℕ) (a : S.GradedPiece k n) :
    S.completedGradedAlgEquiv k (DirectSum.of (S.GradedPiece k) n a) =
      DirectSum.of (S.FormalGradedPiece k) n (S.completedPieceEquiv k n a) := S.completedGradedAlgEquiv_of k n a
example (a b : S.TangentAlgebra k) :
    S.completedGradedAlgEquiv k (a*b) = S.completedGradedAlgEquiv k a*S.completedGradedAlgEquiv k b := map_mul _ _ _
example (c : k) : S.completedGradedAlgEquiv k (algebraMap k (S.TangentAlgebra k) c) =
    algebraMap k (S.FormalTangentAlgebra k) c := (S.completedGradedAlgEquiv k).commutes c
example (K : Type*) [Field K] : (S.formalMaximalIdeal K).IsMaximal := S.formalMaximalIdeal_isMaximal K
end Generic

section Transport
variable (S : NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]
example : S.completedGradedAlgEquiv k (S.xElement k)=S.formalInitialMonomial k S.multiplicityExponent := S.completedGradedAlgEquiv_x k
example (a : S.TangentAlgebra k) : S.completedGradedAlgEquiv k (S.xMultiply k a)=
    S.formalXMultiply k (S.completedGradedAlgEquiv k a) := S.completedGradedAlgEquiv_xMultiply k a
example : (S.xMultiply k).ker ≃ₗ[k] (S.formalXMultiply k).ker := S.completedKernelEquiv k
example : S.HeadAlgebra k ≃ₐ[k] S.FormalHeadAlgebra k := S.completedHeadAlgEquiv k
example : S.AperyAlgebra k ≃ₐ[k] S.FormalAperyAlgebra k := S.completedAperyAlgEquiv k
example (a : S.TangentAlgebra k) : S.completedHeadAlgEquiv k (S.toHeadAlgebra k a)=
    Ideal.Quotient.mk (S.formalXIdeal k) (S.completedGradedAlgEquiv k a) := S.completedHeadAlgEquiv_mk k a
end Transport

namespace CompletedExamples
open AperyQuotientExamples

theorem naturals_order (n : ℕ) : naturals.order n=n := by
  have hl := naturals.length_le_order (show naturals.HasLength n n from
    ⟨fun _ => 1,fun _ => ⟨by trivial,by norm_num⟩,by simp⟩)
  have hu := naturals.order_bound (show n∈naturals from trivial)
  rw [naturals_m,mul_one] at hu
  omega

def allSeries (k : Type*) [CommRing k] (f : PowerSeries k) : naturals.FormalSemigroupRing k :=
  ⟨f,by intro n hn; exact (hn trivial).elim⟩

def infiniteTail (k : Type*) [CommRing k] (n : ℕ) : naturals.FormalSemigroupRing k :=
  allSeries k (PowerSeries.X^n * PowerSeries.mk (fun _ => 1))

example (k : Type*) [CommRing k] (n : ℕ) : infiniteTail k n ∈ naturals.formalMaximalIdeal k ^ n := by
  rw [naturals.mem_formalMaximalIdeal_pow]
  intro x hx
  rw [naturals_order] at hx
  change PowerSeries.coeff x.val (PowerSeries.X^n*PowerSeries.mk (fun _ => (1:k)))=0
  rw [PowerSeries.coeff_X_pow_mul']
  have hn : ¬n≤x.val := by omega
  simp [hn]

example (n : ℕ) : naturals.completedGradedAlgEquiv ℚ (naturals.initialMonomial ℚ ⟨n,by trivial⟩) =
    naturals.formalInitialMonomial ℚ ⟨n,by trivial⟩ := naturals.completedGradedAlgEquiv_initial ℚ _

open Run12Fixtures

/-- The genuine terminal survives the natural comparison and remains killed by x. -/
example : changing.formalXMultiply (ZMod 2) (changing.formalInitialMonomial (ZMod 2) v26)=0 := by
  rw [← changing.completedGradedAlgEquiv_initial,← changing.completedGradedAlgEquiv_xMultiply]
  have hd := changing.xMultiply_initial_dead (ZMod 2) v26 ((changing.not_live_iff_terminal v26).2 terminal_26)
  rw [hd,map_zero]

example : changing.formalInitialMonomial ℚ v15 * changing.formalInitialMonomial ℚ v26 =
    changing.formalInitialMonomial ℚ v41 := by
  rw [← changing.completedGradedAlgEquiv_initial,← changing.completedGradedAlgEquiv_initial,
    ← map_mul,changing.initialMonomial_mul_live ℚ v15 v26 (by
      change changing.order 41=changing.order 15+changing.order 26
      rw [order_41,order_15,order_26]),changing.completedGradedAlgEquiv_initial]
  rfl

end CompletedExamples
