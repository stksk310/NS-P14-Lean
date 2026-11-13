module
public import NSP14.Endpoint.StandardArtinGrading
public import NSP14.Homological.GradedBetti
@[expose] public section
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped Classical
open NSP14.Homological
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

/-- Monomial membership is determined coefficient by coefficient in the actual ideal. -/
def IsMonomial (I : Ideal (MvPolynomial (Fin q) k)) : Prop :=
  ∀ f ∈ I, ∀ v ∈ f.support, MvPolynomial.monomial v (1:k) ∈ I

/-- The lex segment condition uses one ideal, with X 0 > X 1 > ... . -/
def IsLex (I : Ideal (MvPolynomial (Fin q) k)) : Prop :=
  IsMonomial k q I ∧ ∀ (v w : Fin q →₀ ℕ), v.degree=w.degree →
    MonomialOrder.lex.toSyn v ≤ MonomialOrder.lex.toSyn w →
    MvPolynomial.monomial v (1:k) ∈ I → MvPolynomial.monomial w (1:k) ∈ I

/-- Divisibility-minimal monomial generators, not an arbitrary presentation. -/
def MinimalGenerator (I : Ideal (MvPolynomial (Fin q) k)) (v : Fin q →₀ ℕ) : Prop :=
  MvPolynomial.monomial v (1:k) ∈ I ∧
    ∀ w : Fin q →₀ ℕ, w ≤ v → MvPolynomial.monomial w (1:k) ∈ I → w=v

/-- Variable numbers are one-based; the empty monomial has maxVariable 0. -/
def maxVariable (v : Fin q →₀ ℕ) : ℕ := v.support.sup (fun i => i.val+1)

noncomputable def quotientHilbert (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (n : ℕ) : ℕ :=
  Module.finrank k ((NSP14.Endpoint.artinGrading k (Fin q) I hI).piece n)

noncomputable def quotientGradedBetti (I : Ideal (MvPolynomial (Fin q) k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (i : ℕ) (j : ℤ) : ℕ :=
  gradedBetti k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I)
    (NSP14.Endpoint.artinGrading k (Fin q) I hI) i j
end NSP14.Lex
