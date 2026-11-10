module

public import NSP14.Semigroup.IdealPowers
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k]

/-- The actual nth ideal power, viewed as a coefficient-module. -/
noncomputable def powerModule (n : ℕ) : Submodule k (S.SemigroupRing k) :=
  (S.positiveIdeal k ^ n).restrictScalars k

/-- The next ideal power inside the nth power. -/
noncomputable def nextPower (n : ℕ) : Submodule k (S.powerModule k n) :=
  (S.powerModule k (n + 1)).comap (S.powerModule k n).subtype

/-- A homogeneous piece of the associated graded of the algebraic positive ideal. -/
abbrev GradedPiece (n : ℕ) := (S.powerModule k n) ⧸ (S.nextPower k n)

/-- Exponents of monomials whose exact ideal-adic order is n. -/
def DegreeExponent (n : ℕ) := {x : S.carrier // S.order x.val = n}

noncomputable def leadingMap (n : ℕ) :
    S.powerModule k n →ₗ[k] (S.DegreeExponent n →₀ k) :=
  (Finsupp.lsubtypeDomain {x : S.carrier | S.order x.val = n}).comp
    ((AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp (S.powerModule k n).subtype)

theorem leadingMap_apply (n : ℕ) (f : S.powerModule k n) (x : S.DegreeExponent n) :
    S.leadingMap k n f x = f.val.coeff x.val := rfl

theorem leadingMap_ker (n : ℕ) : (S.leadingMap k n).ker = S.nextPower k n := by
  ext f
  change S.leadingMap k n f = 0 ↔ f.val ∈ S.positiveIdeal k ^ (n + 1)
  rw [S.mem_positiveIdeal_pow]
  constructor
  · intro h x hx
    by_cases heq : S.order x.val = n
    · exact congrArg (fun g : S.DegreeExponent n →₀ k => g ⟨x, heq⟩) h
    · exact (S.mem_positiveIdeal_pow k n f.val).1 f.property x (by omega)
  · intro h
    ext x
    exact h x.val (by have := x.property; omega)

theorem leadingMap_surjective (n : ℕ) : Function.Surjective (S.leadingMap k n) := by
  classical
  intro g
  let f : S.SemigroupRing k := AddMonoidAlgebra.ofCoeff g.extendDomain
  have hf : f ∈ S.positiveIdeal k ^ n := by
    rw [← S.orderIdeal_eq_pow, S.mem_orderIdeal_iff]
    intro x hx
    have := g.support_extendDomain_subset hx
    exact le_of_eq this.symm
  refine ⟨⟨f, hf⟩, ?_⟩
  change Finsupp.subtypeDomain _ g.extendDomain = g
  exact Finsupp.subtypeDomain_extendDomain g

/-- The quotient is by the actual next power, not a freely chosen kernel. -/
noncomputable def gradedPieceEquiv (n : ℕ) :
    S.GradedPiece k n ≃ₗ[k] (S.DegreeExponent n →₀ k) :=
  (Submodule.quotEquivOfEq _ _ (S.leadingMap_ker k n).symm).trans
    ((S.leadingMap k n).quotKerEquivOfSurjective (S.leadingMap_surjective k n))

theorem gradedPieceEquiv_mk (n : ℕ) (f : S.powerModule k n) :
    S.gradedPieceEquiv k n (Submodule.Quotient.mk f) = S.leadingMap k n f := rfl

/-- The class of a monomial in any layer where it belongs. -/
noncomputable def monomialClass (n : ℕ) (x : S.carrier) (hx : n ≤ S.order x.val) :
    S.GradedPiece k n :=
  Submodule.Quotient.mk ⟨AddMonoidAlgebra.single x 1,
    by
      change AddMonoidAlgebra.single x (1 : k) ∈ S.positiveIdeal k ^ n
      rw [← S.orderIdeal_eq_pow]
      exact S.single_mem_orderIdeal k n x 1 hx⟩

theorem monomialClass_eq_zero_iff [Nontrivial k] (n : ℕ) (x : S.carrier)
    (hx : n ≤ S.order x.val) :
    S.monomialClass k n x hx = 0 ↔ n < S.order x.val := by
  rw [monomialClass, Submodule.Quotient.mk_eq_zero]
  change AddMonoidAlgebra.single x (1 : k) ∈ S.positiveIdeal k ^ (n + 1) ↔ _
  rw [S.monomial_mem_pow_iff]
  omega

theorem monomialClass_ne_zero [Nontrivial k] (x : S.carrier) :
    S.monomialClass k (S.order x.val) x le_rfl ≠ 0 := by
  intro h
  exact Nat.lt_irrefl _ ((S.monomialClass_eq_zero_iff k _ _ _).1 h)

/-- Product monomials survive exactly when numerical order is additive. -/
theorem product_class_eq_zero_iff [Nontrivial k] (x y : S.carrier) :
    S.monomialClass k (S.order x.val + S.order y.val) (x + y)
      (S.order_add x.property y.property) = 0 ↔
      S.order x.val + S.order y.val < S.order (x.val + y.val) := by
  exact S.monomialClass_eq_zero_iff k _ _ _

end NSP14.NumericalSemigroup
