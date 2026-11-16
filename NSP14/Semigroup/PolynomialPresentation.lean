module

public import NSP14.Semigroup.PolynomialAction

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def headAtomSubalgebra : Subalgebra k (S.HeadAlgebra k) :=
  Algebra.adjoin k (Set.range (fun a : S.NonXAtom => S.headMonomial k a.val))

theorem headMonomial_mem_atomSubalgebra (x : S.carrier) :
    S.headMonomial k x ∈ S.headAtomSubalgebra k := by
  have gen : ∀ n, ∀ hn : n ∈ S, S.headMonomial k ⟨n, hn⟩ ∈ S.headAtomSubalgebra k := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      let z : S.carrier := ⟨n, hn⟩
      by_cases hh : S.XHead n
      · by_cases hz : n = 0
        · subst n
          have he : (⟨0, hn⟩ : S.carrier) = 0 := rfl
          rw [he, headMonomial, S.initialMonomial_zero, map_one]
          exact (S.headAtomSubalgebra k).one_mem
        obtain ⟨a, v, ha, heq, hlive⟩ := S.atomic_live_split z (by change 0 < n; omega)
        have hval : n = a.val + v.val := congrArg Subtype.val heq
        have hm : a.val ≠ S.multiplicity := by
          intro ham
          apply hh.2
          refine ⟨v.val, v.property, by omega, ?_⟩
          have haord := S.atom_order ha
          rw [← hval] at hlive
          omega
        have hvlt : v.val < n := by have hapos := ha.2.1; omega
        have hv := ih v.val hvlt v.property
        have ham : S.headMonomial k a ∈ S.headAtomSubalgebra k :=
          Algebra.subset_adjoin ⟨(⟨a, ha, hm⟩ : S.NonXAtom), rfl⟩
        have hp := (S.headAtomSubalgebra k).mul_mem ham hv
        have he : S.headMonomial k a * S.headMonomial k v = S.headMonomial k z :=
          (S.headMonomial_mul_live k a v hlive).trans (congrArg (S.headMonomial k) heq.symm)
        exact he ▸ hp
      · rw [S.headMonomial_zero_of_not_head k z hh]
        exact (S.headAtomSubalgebra k).zero_mem
  exact gen x.val x.property

theorem head_atom_adjoin_top : S.headAtomSubalgebra k = ⊤ := by
  apply top_unique
  intro a _
  rw [← S.head_expansion k a, Finsupp.sum]
  apply (S.headAtomSubalgebra k).sum_mem
  intro x _
  apply (S.headAtomSubalgebra k).smul_mem
  exact (S.headMonomial_eq_basis k x) ▸ S.headMonomial_mem_atomSubalgebra k x.val

omit [Nontrivial k] in
theorem polynomialToA_eq_aeval : S.polynomialToA k =
    MvPolynomial.aeval (fun a : S.NonXAtom => S.headMonomial k a.val) := by
  apply MvPolynomial.algHom_ext
  intro a
  rw [S.polynomialToA_X, MvPolynomial.aeval_X]

theorem polynomialToA_surjective : Function.Surjective (S.polynomialToA k) := by
  have hr : (S.polynomialToA k).range = ⊤ := by
    rw [S.polynomialToA_eq_aeval, ← Algebra.adjoin_range_eq_range_aeval]
    exact S.head_atom_adjoin_top k
  intro a
  have ha : a ∈ (S.polynomialToA k).range := by rw [hr]; trivial
  exact ha

theorem polynomialToQ_surjective : Function.Surjective (S.polynomialToQ k) := by
  intro q
  obtain ⟨a, ha⟩ := Ideal.Quotient.mkₐ_surjective k (S.nonAperyIdeal k) q
  obtain ⟨p, hp⟩ := S.polynomialToA_surjective k a
  refine ⟨p, ?_⟩
  change Ideal.Quotient.mk _ (S.polynomialToA k p) = q
  rw [hp]
  exact ha

end NSP14.NumericalSemigroup
