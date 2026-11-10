module
public import NSP14.Homological.Presentation
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NSP14.NumericalSemigroup) (k : Type) [Field k]

/-- The algebraic semigroup ring presentation on the same actual minimal
atoms. This ring is distinct from its tangent cone. -/
noncomputable def fullPolynomialToSemigroupRing : S.FullPolynomialRing k →ₐ[k] S.SemigroupRing k :=
  MvPolynomial.aeval (fun a => AddMonoidAlgebra.single a.val (1 : k))

noncomputable def semigroupAtomSubalgebra : Subalgebra k (S.SemigroupRing k) :=
  Algebra.adjoin k (Set.range (fun a : S.AtomExponent => AddMonoidAlgebra.single a.val (1 : k)))

theorem semigroupMonomial_mem_atoms (x : S.carrier) :
    AddMonoidAlgebra.single x (1 : k) ∈ S.semigroupAtomSubalgebra k := by
  have gen : ∀ n, ∀ hn : n ∈ S,
      AddMonoidAlgebra.single (⟨n,hn⟩ : S.carrier) (1 : k) ∈ S.semigroupAtomSubalgebra k := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      let z : S.carrier := ⟨n,hn⟩
      by_cases hz : n=0
      · subst n
        change (1 : S.SemigroupRing k) ∈ _
        exact (S.semigroupAtomSubalgebra k).one_mem
      obtain ⟨a,v,ha,he,_⟩ := S.atomic_live_split z (by change 0 < n;omega)
      have hv : v.val < n := by
        have h := congrArg Subtype.val he
        have hp := ha.2.1
        change n=a.val+v.val at h
        omega
      have ham : AddMonoidAlgebra.single a (1 : k) ∈ S.semigroupAtomSubalgebra k :=
        Algebra.subset_adjoin ⟨(⟨a,ha⟩ : S.AtomExponent),rfl⟩
      have h := (S.semigroupAtomSubalgebra k).mul_mem ham (ih v.val hv v.property)
      rw [AddMonoidAlgebra.single_mul_single,one_mul,← he] at h
      exact h
  exact gen x.val x.property

theorem semigroupAtomSubalgebra_top : S.semigroupAtomSubalgebra k=⊤ := by
  apply top_unique
  intro a _
  rw [← a.sum_coeff_single]
  apply (S.semigroupAtomSubalgebra k).sum_mem
  intro x _
  have h := (S.semigroupAtomSubalgebra k).smul_mem (S.semigroupMonomial_mem_atoms k x) (a.coeff x)
  simpa only [AddMonoidAlgebra.smul_single,smul_eq_mul,mul_one] using h

theorem fullPolynomialToSemigroupRing_surjective :
    Function.Surjective (S.fullPolynomialToSemigroupRing k) := by
  have h : (S.fullPolynomialToSemigroupRing k).range=⊤ := by
    rw [fullPolynomialToSemigroupRing,← Algebra.adjoin_range_eq_range_aeval]
    exact S.semigroupAtomSubalgebra_top k
  intro a
  exact (show a ∈ (S.fullPolynomialToSemigroupRing k).range by rw [h];trivial)

noncomputable instance fullPolynomialAlgebraSemigroupRing :
    Algebra (S.FullPolynomialRing k) (S.SemigroupRing k) :=
  (S.fullPolynomialToSemigroupRing k).toRingHom.toAlgebra

noncomputable instance fullPolynomialFiniteSemigroupRing :
    Module.Finite (S.FullPolynomialRing k) (S.SemigroupRing k) :=
  Module.Finite.of_surjective (Algebra.linearMap (S.FullPolynomialRing k) (S.SemigroupRing k))
    (S.fullPolynomialToSemigroupRing_surjective k)
end NSP14.NumericalSemigroup
