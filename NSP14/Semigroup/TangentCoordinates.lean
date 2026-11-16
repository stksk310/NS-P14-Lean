module

public import NSP14.Semigroup.TangentAlgebra
public import NSP14.Semigroup.GradedBasis

@[expose] public section

open scoped DirectSum

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

/-- Every actual exponent occurs in exactly its own order degree. -/
noncomputable def degreeSigmaEquiv : (Σ n, S.DegreeExponent n) ≃ S.carrier where
  toFun x := x.2.val
  invFun x := ⟨S.order x.val, ⟨x, rfl⟩⟩
  left_inv := by rintro ⟨n, x, hx⟩; cases hx; rfl
  right_inv _ := rfl

/-- Global coordinates for the actual direct sum of ideal-power quotients. -/
noncomputable def tangentCoordinates : S.TangentAlgebra k ≃ₗ[k] (S.carrier →₀ k) :=
  ((DFinsupp.mapRange.linearEquiv (fun n => S.gradedPieceEquiv k n)).trans
    (sigmaFinsuppLequivDFinsupp k).symm).trans
    (Finsupp.domLCongr (R := k) (M := k) S.degreeSigmaEquiv)

theorem tangentCoordinates_apply (g : S.TangentAlgebra k) (x : S.carrier) :
    S.tangentCoordinates k g x =
      S.gradedPieceEquiv k (S.order x.val) (g (S.order x.val)) ⟨x, rfl⟩ := by
  simp [tangentCoordinates, Finsupp.domLCongr_apply, degreeSigmaEquiv]
  rfl

/-- The initial form of an actual semigroup monomial, in the whole graded ring. -/
noncomputable def initialMonomial (x : S.carrier) : S.TangentAlgebra k :=
  DirectSum.of (S.GradedPiece k) (S.order x.val) (S.monomialClass k _ x le_rfl)

theorem tangentCoordinates_initial (x : S.carrier) :
    S.tangentCoordinates k (S.initialMonomial k x) = Finsupp.single x 1 := by
  classical
  have hb := (congrArg (S.gradedPieceEquiv k (S.order x.val))
    (S.gradedPieceBasis_eq_monomial k (S.order x.val) ⟨x, rfl⟩)).symm.trans
    (S.gradedPieceBasis_coordinates k (S.order x.val) ⟨x, rfl⟩)
  change (Finsupp.domLCongr (R := k) (M := k) S.degreeSigmaEquiv)
    ((sigmaFinsuppLequivDFinsupp k).symm
      (DFinsupp.mapRange (fun n a => S.gradedPieceEquiv k n a)
        (fun n => (S.gradedPieceEquiv k n).map_zero)
        (DFinsupp.single (S.order x.val) (S.monomialClass k _ x le_rfl)))) = _
  rw [DFinsupp.mapRange_single, hb]
  have hs : (sigmaFinsuppLequivDFinsupp k).symm
      (DFinsupp.single (S.order x.val) (Finsupp.single (⟨x, rfl⟩ : S.DegreeExponent _) (1 : k))) =
      Finsupp.single (⟨S.order x.val, ⟨x, rfl⟩⟩ : Σ n, S.DegreeExponent n) (1 : k) := by
    apply (sigmaFinsuppLequivDFinsupp k).symm_apply_eq.mpr
    exact (sigmaFinsuppEquivDFinsupp_single
      (⟨S.order x.val, ⟨x, rfl⟩⟩ : Σ n, S.DegreeExponent n) (1 : k)).symm
  rw [hs]
  simp [degreeSigmaEquiv]

noncomputable def tangentBasis : Module.Basis S.carrier k (S.TangentAlgebra k) :=
  Finsupp.basisSingleOne.map (S.tangentCoordinates k).symm

theorem tangentBasis_eq_initial (x : S.carrier) :
    S.tangentBasis k x = S.initialMonomial k x := by
  apply (S.tangentCoordinates k).injective
  simp [tangentBasis, S.tangentCoordinates_initial]

theorem initialMonomial_ne_zero [Nontrivial k] (x : S.carrier) : S.initialMonomial k x ≠ 0 := by
  intro h
  have := congrArg (S.tangentCoordinates k) h
  rw [S.tangentCoordinates_initial, map_zero] at this
  exact Finsupp.single_ne_zero.mpr one_ne_zero this

theorem initialMonomial_mul_eq_zero_iff [Nontrivial k] (x y : S.carrier) :
    S.initialMonomial k x * S.initialMonomial k y = 0 ↔
      S.order x.val + S.order y.val < S.order (x.val + y.val) := by
  rw [initialMonomial, initialMonomial, S.tangent_of_mul]
  have hinj := DirectSum.of_injective (β := S.GradedPiece k) (S.order x.val + S.order y.val)
  rw [← map_zero (DirectSum.of (S.GradedPiece k) (S.order x.val + S.order y.val)), hinj.eq_iff]
  exact S.gradedMul_monomial_eq_zero_iff k x y

theorem initialMonomial_mul_live (x y : S.carrier)
    (h : S.order (x.val + y.val) = S.order x.val + S.order y.val) :
    S.initialMonomial k x * S.initialMonomial k y = S.initialMonomial k (x + y) := by
  rw [initialMonomial, initialMonomial, S.tangent_of_mul, S.gradedMul_monomial]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply S.homogeneous_mk_eq k h.symm
  rfl

end NSP14.NumericalSemigroup
