module

public import NSP14.Semigroup.TangentAlgebra
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Algebra.Basic

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

noncomputable instance pieceModule (n : ℕ) : Module k (S.GradedPiece k n) :=
  inferInstanceAs (Module k ((S.powerModule k n) ⧸ S.nextPower k n))

/-- Scalars in the zeroth ideal-power quotient. -/
noncomputable def scalarClass : k →ₗ[k] S.GradedPiece k 0 where
  toFun c := Submodule.Quotient.mk (S.zeroRepresentative k (AddMonoidAlgebra.single 0 c))
  map_add' := by
    intro c d
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact AddMonoidAlgebra.single_add _ _ _
  map_smul' := by
    intro c d
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact (AddMonoidAlgebra.smul_single c (0 : S.carrier) d).symm

noncomputable instance pieceGAlgebra : DirectSum.GAlgebra k (S.GradedPiece k) where
  toFun := (S.scalarClass k).toAddMonoidHom
  map_one := rfl
  map_mul := by
    intro c d
    change GradedMonoid.mk (A := S.GradedPiece k) 0 (Submodule.Quotient.mk _) =
      GradedMonoid.mk (0 + 0) (S.gradedMul k 0 0 (Submodule.Quotient.mk _) (Submodule.Quotient.mk _))
    rw [S.gradedMul_mk]
    apply S.homogeneous_mk_eq k rfl
    simp [zeroRepresentative]
  commutes := by intro r x; exact mul_comm _ _
  smul_def := by
    rintro r ⟨n, a⟩
    induction a using Submodule.Quotient.induction_on with
    | _ f =>
      change GradedMonoid.mk (A := S.GradedPiece k) n (r • Submodule.Quotient.mk f) =
        GradedMonoid.mk (0 + n) (S.gradedMul k 0 n (Submodule.Quotient.mk _) (Submodule.Quotient.mk f))
      rw [← Submodule.Quotient.mk_smul, S.gradedMul_mk]
      apply S.homogeneous_mk_eq k (Nat.zero_add n).symm
      apply AddMonoidAlgebra.coeff_injective
      ext x
      simp [zeroRepresentative, AddMonoidAlgebra.coeff_single_zero_mul]

noncomputable instance tangentAlgebraStructure : Algebra k (S.TangentAlgebra k) :=
  DirectSum.instAlgebra k (S.GradedPiece k)

end NSP14.NumericalSemigroup
