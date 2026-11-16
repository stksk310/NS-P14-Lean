module
public import NSP14.Lex.Ideal
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Classical
open NSP14.Homological
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
  (I : Ideal (MvPolynomial (Fin q) k))
  (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))

/-- Degree finiteness does not assume the whole quotient is Artinian. -/
theorem standard_degree_finite (n : ℤ) :
    Finite {p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=n} := by
  let f : {p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=n} →
      {v : Fin q →₀ ℕ // v.degree≤n.toNat} := fun p => ⟨p.val.val,by
        have := p.property
        omega⟩
  let : Finite {v : Fin q →₀ ℕ // v.degree≤n.toNat} :=
    (Finsupp.finite_of_degree_le n.toNat).to_subtype
  apply Finite.of_injective f
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : {v : Fin q →₀ ℕ // v.degree≤n.toNat} => z.val) h

noncomputable instance quotient_piece_finite (n : ℤ) :
    Module.Finite k ((NSP14.Endpoint.artinGrading k (Fin q) I hI).piece n) := by
  let := standard_degree_finite k q I n
  change Module.Finite k ({p : StandardExponent MonomialOrder.degLex I // (p.val.degree : ℤ)=n} →₀ k)
  infer_instance

/-- The actual quotient's derived Tor is the finite sum of its internal-degree pieces. -/
theorem quotient_total_eq_graded_sum (i : ℕ) :
    ∃ s : Finset ℤ,
      (∀ j∉s,quotientGradedBetti k q I hI i j=0) ∧
      totalBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I) i=
        ∑ j∈s,quotientGradedBetti k q I hI i j := by
  obtain ⟨s,hs,he⟩ := gradedBetti_total k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I)
    (NSP14.Endpoint.artinGrading k (Fin q) I hI) i
  refine ⟨s,fun j hj => ?_,he⟩
  let := ModuleCat.subsingleton_of_isZero (hs j hj)
  exact Module.finrank_zero_of_subsingleton
end NSP14.Lex
