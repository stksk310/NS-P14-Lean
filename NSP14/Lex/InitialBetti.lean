module
public import NSP14.Endpoint.InitialDiagonal
public import NSP14.Homological.FiniteKoszulEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))
  (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))

/-- Actual graded Betti numbers cannot decrease on passing to the actual
degLex initial ideal, over every field, in every row and internal degree.
The proof uses the original and initial quotients' actual signed Koszul
matrices and genuine diagonal-block rank inequalities. -/
theorem quotientGradedBetti_initial_le (i : ℕ) (t : ℤ) :
    quotientGradedBetti k q I hI i t ≤
      quotientGradedBetti k q (initialIdeal k q MonomialOrder.degLex I)
        (initialIdeal_homogeneous k q MonomialOrder.degLex I) i t := by
  let J := initialIdeal k q MonomialOrder.degLex I
  let hJ := initialIdeal_homogeneous k q MonomialOrder.degLex I
  let A := gradedKoszulComplex k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) I)
    (NSP14.Endpoint.artinGrading k (Fin q) I hI) (variableList k (Fin q)) t
  let B := gradedKoszulComplex k (Fin q) (NSP14.Endpoint.artinModule k (Fin q) J)
    (NSP14.Endpoint.artinGrading k (Fin q) J hJ) (variableList k (Fin q)) t
  let : ∀ n,Module.Finite k (A.X n) := fun n => NSP14.Endpoint.artinGradedChain_finite k q I hI t n
  let : ∀ n,Module.Finite k (B.X n) := fun n => NSP14.Endpoint.artinGradedChain_finite k q J hJ t n
  have hdim (n : ℕ) : Module.finrank k (B.X n)=Module.finrank k (A.X n) :=
    (NSP14.Endpoint.initialGradedChainEquiv k q I hI t n).finrank_eq
  have hr (n : ℕ) : chainBoundaryRank k B n ≤ chainBoundaryRank k A n := by
    cases n with
    | zero => simp only [chainBoundaryRank_zero,le_refl]
    | succ n =>
      rw [chainBoundaryRank_succ,chainBoundaryRank_succ]
      have hA : A.d (n+1) n=ModuleCat.ofHom (NSP14.Endpoint.artinBoundaryMap k q I hI t n) := by
        dsimp only [A,gradedKoszulComplex,NSP14.Endpoint.artinBoundaryMap]
        exact ChainComplex.of_d _ _ n
      have hB : B.d (n+1) n=ModuleCat.ofHom (NSP14.Endpoint.artinBoundaryMap k q J hJ t n) := by
        dsimp only [B,gradedKoszulComplex,NSP14.Endpoint.artinBoundaryMap]
        exact ChainComplex.of_d _ _ n
      have hRA := congrArg (fun f : A.X (n+1) ⟶ A.X n => Module.finrank k f.hom.range) hA
      have hRB := congrArg (fun f : B.X (n+1) ⟶ B.X n => Module.finrank k f.hom.range) hB
      calc
        _=Module.finrank k (NSP14.Endpoint.artinBoundaryMap k q J hJ t n).range := hRB
        _≤Module.finrank k (NSP14.Endpoint.artinBoundaryMap k q I hI t n).range :=
          NSP14.Endpoint.initial_graded_boundary_rank_le k q I hI t n
        _=Module.finrank k (A.d (n+1) n).hom.range := hRA.symm
  have ha := chain_homology_rank k A i
  have hb := chain_homology_rank k B i
  have hr0 := hr i
  have hr1 := hr (i+1)
  have hd := hdim i
  change Module.finrank k (A.homology i) ≤ Module.finrank k (B.homology i)
  omega
end NSP14.Lex
