module

public import NSP14.Semigroup.FormalTangentAlgebra
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Algebra.Basic

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

noncomputable instance formalPieceModule (n : ℕ) : Module k (S.FormalGradedPiece k n) :=
  inferInstanceAs (Module k ((S.formalPowerModule k n) ⧸ S.formalNextPower k n))

/-- Scalars in the zeroth ideal-power quotient. -/
noncomputable def formalScalarClass : k →ₗ[k] S.FormalGradedPiece k 0 where
  toFun c := Submodule.Quotient.mk (S.formalZeroRepresentative k (algebraMap k (S.FormalSemigroupRing k) c))
  map_add' := by
    intro c d
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact map_add (algebraMap k (S.FormalSemigroupRing k)) c d
  map_smul' := by
    intro c d
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact (Algebra.linearMap k (S.FormalSemigroupRing k)).map_smul c d

noncomputable instance formalPieceGAlgebra : DirectSum.GAlgebra k (S.FormalGradedPiece k) where
  toFun := (S.formalScalarClass k).toAddMonoidHom
  map_one := rfl
  map_mul := by
    intro c d
    change GradedMonoid.mk (A := S.FormalGradedPiece k) 0 (Submodule.Quotient.mk _) =
      GradedMonoid.mk (0 + 0) (S.formalGradedMul k 0 0 (Submodule.Quotient.mk _) (Submodule.Quotient.mk _))
    rw [S.formalGradedMul_mk]
    apply S.formal_homogeneous_mk_eq k rfl
    simp [formalZeroRepresentative]
  commutes := by intro r x; exact mul_comm _ _
  smul_def := by
    rintro r ⟨n, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      change GradedMonoid.mk (A := S.FormalGradedPiece k) n (r • Submodule.Quotient.mk f) =
        GradedMonoid.mk (0 + n) (S.formalGradedMul k 0 n (Submodule.Quotient.mk _) (Submodule.Quotient.mk f))
      rw [← Submodule.Quotient.mk_smul, S.formalGradedMul_mk]
      apply S.formal_homogeneous_mk_eq k (Nat.zero_add n).symm
      exact Algebra.smul_def r f.val

noncomputable instance formalTangentAlgebraStructure : Algebra k (S.FormalTangentAlgebra k) :=
  DirectSum.instAlgebra k (S.FormalGradedPiece k)

end NSP14.NumericalSemigroup
