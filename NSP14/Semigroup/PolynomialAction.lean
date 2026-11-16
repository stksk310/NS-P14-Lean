module

public import NSP14.Semigroup.HeadGradedAlgebra
public import NSP14.Semigroup.JumpBounds
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Algebra.Tower

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

def NonXAtom := {a : S.carrier // S.IsAtom a.val ∧ a.val ≠ S.multiplicity}

noncomputable def nonXAtomEquivAtoms : S.NonXAtom ≃ ↥(S.atoms.erase S.multiplicity) where
  toFun a := ⟨a.val.val, Finset.mem_erase.mpr ⟨a.property.2, (S.mem_atoms_iff _).2 a.property.1⟩⟩
  invFun a := ⟨⟨a.val, S.atoms_mem (Finset.mem_erase.mp a.property).2⟩,
    (S.mem_atoms_iff _).1 (Finset.mem_erase.mp a.property).2, (Finset.mem_erase.mp a.property).1⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance nonXAtomFintype : Fintype S.NonXAtom :=
  Fintype.ofEquiv ↥(S.atoms.erase S.multiplicity) S.nonXAtomEquivAtoms.symm

theorem nonXAtom_card : Fintype.card S.NonXAtom = S.embeddingDimension - 1 := by
  rw [Fintype.card_congr S.nonXAtomEquivAtoms, Fintype.card_coe, S.nonmultiplicity_atoms_card]

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- The single polynomial ring S₀, indexed by the actual non-multiplicity atoms. -/
abbrev PolynomialRing := MvPolynomial S.NonXAtom k

noncomputable def polynomialToG : S.PolynomialRing k →ₐ[k] S.TangentAlgebra k :=
  MvPolynomial.aeval (fun a => S.initialMonomial k a.val)

noncomputable def polynomialToA : S.PolynomialRing k →ₐ[k] S.HeadAlgebra k :=
  (S.toHeadAlgebra k).comp (S.polynomialToG k)

noncomputable def polynomialToQ : S.PolynomialRing k →ₐ[k] S.AperyAlgebra k :=
  (S.toAperyAlgebra k).comp (S.polynomialToG k)

noncomputable instance polynomialAlgebraG : Algebra (S.PolynomialRing k) (S.TangentAlgebra k) :=
  (S.polynomialToG k).toRingHom.toAlgebra

noncomputable instance polynomialScalarTowerG : IsScalarTower k (S.PolynomialRing k) (S.TangentAlgebra k) :=
  IsScalarTower.of_algebraMap_eq (fun c => (S.polynomialToG k).commutes c |>.symm)

omit [Nontrivial k] in
theorem polynomialToG_X (a : S.NonXAtom) :
    S.polynomialToG k (MvPolynomial.X a) = S.initialMonomial k a.val := MvPolynomial.aeval_X _ a

omit [Nontrivial k] in
theorem polynomialToA_X (a : S.NonXAtom) :
    S.polynomialToA k (MvPolynomial.X a) = S.headMonomial k a.val := by
  change S.toHeadAlgebra k (S.polynomialToG k (MvPolynomial.X a)) = _
  rw [S.polynomialToG_X]
  rfl

theorem polynomialToQ_X (a : S.NonXAtom) :
    S.polynomialToQ k (MvPolynomial.X a) = S.qMonomial k a.val := by
  change S.toAperyAlgebra k (S.polynomialToG k (MvPolynomial.X a)) = _
  rw [S.polynomialToG_X, S.toAperyAlgebra_initial]

/-- The ideal of the actual ring G annihilating x; its carrier is the existing actual T. -/
noncomputable def terminalIdeal : Ideal (S.TangentAlgebra k) where
  carrier := {a | a * S.xElement k = 0}
  zero_mem' := zero_mul _
  add_mem' := by
    intro a b ha hb
    change a * S.xElement k = 0 at ha
    change b * S.xElement k = 0 at hb
    change (a + b) * S.xElement k = 0
    rw [add_mul, ha, hb, zero_add]
  smul_mem' r a ha := by
    change (r * a) * S.xElement k = 0
    rw [mul_assoc, ha, mul_zero]

omit [Nontrivial k] in
theorem terminalIdeal_restrictScalars :
    (S.terminalIdeal k).restrictScalars k = (S.xMultiply k).ker := rfl

noncomputable instance terminalPolynomialModule :
    Module (S.PolynomialRing k) ((S.xMultiply k).ker) :=
  inferInstanceAs (Module (S.PolynomialRing k) (S.terminalIdeal k))

noncomputable instance nonAperyPolynomialModule :
    Module (S.PolynomialRing k) ((S.nonAperyIdeal k).restrictScalars k) :=
  inferInstanceAs (Module (S.PolynomialRing k) (S.nonAperyIdeal k))

omit [Nontrivial k] in
theorem polynomial_smul_G (p : S.PolynomialRing k) (a : S.TangentAlgebra k) :
    p • a = S.polynomialToG k p * a := rfl

omit [Nontrivial k] in
theorem polynomial_smul_T (p : S.PolynomialRing k) (a : (S.xMultiply k).ker) :
    (p • a).val = S.polynomialToG k p * a.val := rfl

omit [Nontrivial k] in
theorem polynomial_smul_A (p : S.PolynomialRing k) (a : S.HeadAlgebra k) :
    p • a = S.polynomialToA k p * a := rfl

theorem polynomial_smul_N (p : S.PolynomialRing k) (a : (S.nonAperyIdeal k).restrictScalars k) :
    (p • a).val = S.polynomialToA k p * a.val := rfl

theorem polynomial_smul_Q (p : S.PolynomialRing k) (a : S.AperyAlgebra k) :
    p • a = S.polynomialToQ k p * a := rfl

noncomputable instance polynomialScalarTowerA : IsScalarTower k (S.PolynomialRing k) (S.HeadAlgebra k) :=
  IsScalarTower.of_algebraMap_eq (fun c => (S.polynomialToA k).commutes c |>.symm)

noncomputable instance polynomialScalarTowerQ : IsScalarTower k (S.PolynomialRing k) (S.AperyAlgebra k) :=
  IsScalarTower.of_algebraMap_eq (fun c => (S.polynomialToQ k).commutes c |>.symm)

noncomputable instance polynomialScalarTowerT : IsScalarTower k (S.PolynomialRing k) ((S.xMultiply k).ker) where
  smul_assoc r p a := Subtype.ext (smul_assoc r p a.val)

noncomputable instance polynomialScalarTowerN :
    IsScalarTower k (S.PolynomialRing k) ((S.nonAperyIdeal k).restrictScalars k) where
  smul_assoc r p a := Subtype.ext (smul_assoc r p a.val)

noncomputable def polynomialGtoA : S.TangentAlgebra k →ₗ[S.PolynomialRing k] S.HeadAlgebra k :=
  (Ideal.Quotient.mkₐ (S.PolynomialRing k) (S.xIdeal k)).toLinearMap

noncomputable def polynomialAtoQ : S.HeadAlgebra k →ₗ[S.PolynomialRing k] S.AperyAlgebra k :=
  (Ideal.Quotient.mkₐ (S.PolynomialRing k) (S.nonAperyIdeal k)).toLinearMap

omit [Nontrivial k] in
theorem polynomialToG_X_degree (a : S.NonXAtom) : S.polynomialToG k (MvPolynomial.X a) =
    DirectSum.of (S.GradedPiece k) 1
      (S.monomialClass k 1 a.val (le_of_eq (S.atom_order a.property.1).symm)) := by
  rw [S.polynomialToG_X]
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply S.homogeneous_mk_eq k (S.atom_order a.property.1)
  rfl

end NSP14.NumericalSemigroup
