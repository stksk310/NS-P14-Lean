module
public import NSP14.Endpoint.InitialBoundary
public import NSP14.Homological.FactorRange
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))

/-- The actual initial quotient's chain labels have the very same exponents
and exterior slots as the original quotient's chain labels. -/
noncomputable def initialChainIndexEquiv (t : ℤ) (i : ℕ) :
    ArtinChainIndex k q (Lex.initialIdeal k q MonomialOrder.degLex I) t i ≃ ArtinChainIndex k q I t i where
  toFun a := ⟨(a.val.1,⟨a.val.2.val,by
    rw [←Lex.initialIdeal_standard k q MonomialOrder.degLex I]
    exact a.val.2.property⟩),a.property⟩
  invFun a := ⟨(a.val.1,⟨a.val.2.val,by
    rw [Lex.initialIdeal_standard k q MonomialOrder.degLex I]
    exact a.val.2.property⟩),a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem initialChainIndexEquiv_term (t : ℤ) (i : ℕ)
    (a : ArtinChainIndex k q (Lex.initialIdeal k q MonomialOrder.degLex I) t i) :
    artinChainTerm k q I t i (initialChainIndexEquiv k q I t i a)=
      artinChainTerm k q (Lex.initialIdeal k q MonomialOrder.degLex I) t i a := rfl

theorem initialChainIndexEquiv_symm_term (t : ℤ) (i : ℕ) (a : ArtinChainIndex k q I t i) :
    artinChainTerm k q (Lex.initialIdeal k q MonomialOrder.degLex I) t i
      ((initialChainIndexEquiv k q I t i).symm a)=artinChainTerm k q I t i a := rfl

variable (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))

/-- A field-linear chain-space identification, only for comparing actual
ranks. No chain-map or homology isomorphism is asserted. -/
noncomputable def initialGradedChainEquiv (t : ℤ) (i : ℕ) :
    artinGradedChainSpace k q (Lex.initialIdeal k q MonomialOrder.degLex I)
      (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t i ≃ₗ[k]
    artinGradedChainSpace k q I hI t i :=
  (artinGradedChainBasis k q (Lex.initialIdeal k q MonomialOrder.degLex I)
    (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t i).equiv
      (artinGradedChainBasis k q I hI t i) (initialChainIndexEquiv k q I t i)

include hI in
theorem initialGradedChainEquiv_basis (t : ℤ) (i : ℕ)
    (a : ArtinChainIndex k q (Lex.initialIdeal k q MonomialOrder.degLex I) t i) :
    initialGradedChainEquiv k q I hI t i (artinGradedChainBasis k q
      (Lex.initialIdeal k q MonomialOrder.degLex I) (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t i a)=
      artinGradedChainBasis k q I hI t i (initialChainIndexEquiv k q I t i a) := by
  unfold initialGradedChainEquiv
  exact Module.Basis.equiv_apply _ a _ _

include hI in
theorem initialGradedChainEquiv_symm_basis (t : ℤ) (i : ℕ) (a : ArtinChainIndex k q I t i) :
    (initialGradedChainEquiv k q I hI t i).symm (artinGradedChainBasis k q I hI t i a)=
      artinGradedChainBasis k q (Lex.initialIdeal k q MonomialOrder.degLex I)
        (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t i ((initialChainIndexEquiv k q I t i).symm a) := by
  unfold initialGradedChainEquiv
  rw [Module.Basis.equiv_symm]
  exact Module.Basis.equiv_apply _ a _ _

include hI in
theorem initialGradedChainEquiv_repr (t : ℤ) (i : ℕ)
    (x : artinGradedChainSpace k q (Lex.initialIdeal k q MonomialOrder.degLex I)
      (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t i) (a : ArtinChainIndex k q I t i) :
    (artinGradedChainBasis k q I hI t i).repr (initialGradedChainEquiv k q I hI t i x) a=
      (artinGradedChainBasis k q (Lex.initialIdeal k q MonomialOrder.degLex I)
        (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t i).repr x
          ((initialChainIndexEquiv k q I t i).symm a) := by
  let B := artinGradedChainBasis k q I hI t i
  let C := artinGradedChainBasis k q (Lex.initialIdeal k q MonomialOrder.degLex I)
    (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t i
  let e := initialChainIndexEquiv k q I t i
  have h : (B.reindex e.symm).repr (initialGradedChainEquiv k q I hI t i x)=C.repr x := by
    change (B.reindex e.symm).repr ((B.reindex e.symm).repr.symm (C.repr x))=C.repr x
    exact LinearEquiv.apply_symm_apply _ _
  have he := congrArg (fun c => c (e.symm a)) h
  simp only [Module.Basis.repr_reindex_apply,Equiv.symm_symm,Equiv.apply_symm_apply] at he
  exact he

noncomputable def initialBoundaryTransport (t : ℤ) (i : ℕ) :
    artinGradedChainSpace k q I hI t (i+1) →ₗ[k] artinGradedChainSpace k q I hI t i :=
  (initialGradedChainEquiv k q I hI t i).toLinearMap.comp
    ((gradedKoszulDifferential k (Fin q) (artinModule k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I))
      (artinGrading k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I)
        (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I)) (variableList k (Fin q)) t i).comp
      (initialGradedChainEquiv k q I hI t (i+1)).symm.toLinearMap)

include hI in
theorem initialBoundaryTransport_entry (t : ℤ) (i : ℕ)
    (s : ArtinChainIndex k q I t (i+1)) (r : ArtinChainIndex k q I t i) :
    (artinGradedChainBasis k q I hI t i).repr
      (initialBoundaryTransport k q I hI t i (artinGradedChainBasis k q I hI t (i+1) s)) r=
    (artinGradedChainBasis k q (Lex.initialIdeal k q MonomialOrder.degLex I)
      (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t i).repr
      (gradedKoszulDifferential k (Fin q) (artinModule k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I))
        (artinGrading k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I)
          (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I)) (variableList k (Fin q)) t i
            (artinGradedChainBasis k q (Lex.initialIdeal k q MonomialOrder.degLex I)
              (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I) t (i+1)
                ((initialChainIndexEquiv k q I t (i+1)).symm s)))
                  ((initialChainIndexEquiv k q I t i).symm r) := by
  unfold initialBoundaryTransport
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe]
  rw [initialGradedChainEquiv_repr,initialGradedChainEquiv_symm_basis]

include hI in
theorem initialBoundaryTransport_rank (t : ℤ) (i : ℕ) :
    Module.finrank k (initialBoundaryTransport k q I hI t i).range=
      Module.finrank k (gradedKoszulDifferential k (Fin q)
        (artinModule k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I))
        (artinGrading k (Fin q) (Lex.initialIdeal k q MonomialOrder.degLex I)
          (Lex.initialIdeal_homogeneous k q MonomialOrder.degLex I)) (variableList k (Fin q)) t i).range :=
  factorization_range_finrank k _ _
    (initialGradedChainEquiv k q I hI t (i+1)).symm.toLinearMap
    (initialGradedChainEquiv k q I hI t i).toLinearMap
    (initialGradedChainEquiv k q I hI t (i+1)).symm.surjective
    (initialGradedChainEquiv k q I hI t i).injective rfl
end NSP14.Endpoint
