module
public import NSP14.Endpoint.InitialTransport
public import NSP14.Homological.BasisBlocks
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))

noncomputable def boundaryTermSet (t : ℤ) (i : ℕ) : Finset (MonomialOrder.degLex (σ:=Fin q)).syn :=
  (Set.finite_range (fun a : ArtinChainIndex k q I t i =>
    MonomialOrder.degLex.toSyn (artinChainTerm k q I t i a))).toFinset ∪
  (Set.finite_range (fun a : ArtinChainIndex k q I t (i+1) =>
    MonomialOrder.degLex.toSyn (artinChainTerm k q I t (i+1) a))).toFinset

noncomputable abbrev BoundaryLabel (t : ℤ) (i : ℕ) := ↥(boundaryTermSet k q I t i)

noncomputable def sourceBoundaryLabel (t : ℤ) (i : ℕ) (a : ArtinChainIndex k q I t (i+1)) :
    BoundaryLabel k q I t i :=
  ⟨MonomialOrder.degLex.toSyn (artinChainTerm k q I t (i+1) a),
    Finset.mem_union.mpr (Or.inr ((Set.Finite.mem_toFinset _).mpr ⟨a,rfl⟩))⟩

noncomputable def targetBoundaryLabel (t : ℤ) (i : ℕ) (a : ArtinChainIndex k q I t i) :
    BoundaryLabel k q I t i :=
  ⟨MonomialOrder.degLex.toSyn (artinChainTerm k q I t i a),
    Finset.mem_union.mpr (Or.inl ((Set.Finite.mem_toFinset _).mpr ⟨a,rfl⟩))⟩

variable (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))

noncomputable abbrev artinBoundaryMap (t : ℤ) (i : ℕ) :=
  gradedKoszulDifferential k (Fin q) (artinModule k (Fin q) I) (artinGrading k (Fin q) I hI)
    (variableList k (Fin q)) t i

include hI in
/-- The actual initial-ideal differential, transported only as a field-linear
map, is exactly the literal diagonal part of the original actual differential. -/
theorem initialBoundary_eq_diagonal (t : ℤ) (i : ℕ) :
    initialBoundaryTransport k q I hI t i=
      basisDiagonalMap k (artinGradedChainBasis k q I hI t (i+1)) (sourceBoundaryLabel k q I t i)
        (artinGradedChainBasis k q I hI t i) (targetBoundaryLabel k q I t i) (artinBoundaryMap k q I hI t i) := by
  apply (artinGradedChainBasis k q I hI t (i+1)).ext
  intro s
  apply (artinGradedChainBasis k q I hI t i).repr.injective
  ext r
  rw [initialBoundaryTransport_entry,basisDiagonalMap_coord]
  by_cases hs : artinChainTerm k q I t (i+1) s=artinChainTerm k q I t i r
  · have hl : targetBoundaryLabel k q I t i r=sourceBoundaryLabel k q I t i s :=
      Subtype.ext (congrArg MonomialOrder.degLex.toSyn hs.symm)
    rw [ite_eq_left hl,artinGradedBoundary_sameTerm k q I hI t i s r hs]
    have hs' : artinChainTerm k q (Lex.initialIdeal k q MonomialOrder.degLex I) t (i+1)
        ((initialChainIndexEquiv k q I t (i+1)).symm s)=
        artinChainTerm k q (Lex.initialIdeal k q MonomialOrder.degLex I) t i
          ((initialChainIndexEquiv k q I t i).symm r) := by
      rw [initialChainIndexEquiv_symm_term,initialChainIndexEquiv_symm_term]
      exact hs
    rw [artinGradedBoundary_sameTerm k q (Lex.initialIdeal k q MonomialOrder.degLex I)
      (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t i _ _ hs']
    rfl
  · have hl : targetBoundaryLabel k q I t i r ≠ sourceBoundaryLabel k q I t i s := by
      intro he
      have hv := congrArg Subtype.val he
      change MonomialOrder.degLex.toSyn (artinChainTerm k q I t i r)=
        MonomialOrder.degLex.toSyn (artinChainTerm k q I t (i+1) s) at hv
      exact hs (MonomialOrder.degLex.toSyn.injective hv).symm
    rw [ite_eq_right hl]
    apply artinGradedBoundary_monomial_offTerm k q (Lex.initialIdeal k q MonomialOrder.degLex I)
      (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I)
      (Lex.initialIdeal_isMonomial k q MonomialOrder.degLex I) t i
    intro he
    rw [initialChainIndexEquiv_symm_term,initialChainIndexEquiv_symm_term] at he
    exact hs he

include hI in
/-- The actual initial-ideal boundary rank is no larger than the original
actual boundary rank, at every internal and homological degree. -/
theorem initial_graded_boundary_rank_le (t : ℤ) (i : ℕ) :
    Module.finrank k (gradedKoszulDifferential k (Fin q)
      (artinModule k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I))
      (artinGrading k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I)
        (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I)) (variableList k (Fin q)) t i).range ≤
      Module.finrank k (artinBoundaryMap k q I hI t i).range := by
  rw [←initialBoundaryTransport_rank k q I hI t i,initialBoundary_eq_diagonal]
  let : Fintype (ArtinChainIndex k q I t (i+1)) := Fintype.ofFinite _
  let : Fintype (ArtinChainIndex k q I t i) := Fintype.ofFinite _
  apply basisDiagonalMap_rank
  intro s r hlt
  apply artinGradedBoundary_triangular k q I hI t i s r
  exact hlt
end NSP14.Endpoint
