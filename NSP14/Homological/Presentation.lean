module

public import NSP14.Semigroup.PolynomialGrading
public import NSP14.Semigroup.CompletedTransport
public import Mathlib.Algebra.MvPolynomial.CommRing

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.Homological

/-- The variable type is part of the ring, so source/S₀/cut rings stay distinct. -/
abbrev VariableRing (k σ : Type*) [CommRing k] := MvPolynomial σ k

noncomputable def augmentation (k σ : Type*) [CommRing k] : VariableRing k σ →ₐ[k] k :=
  MvPolynomial.aeval (fun _ => 0)

theorem augmentation_X (k σ : Type*) [CommRing k] (x : σ) :
    augmentation k σ (MvPolynomial.X x)=0 := MvPolynomial.aeval_X _ x

noncomputable def variableOperator (k σ M : Type*) [CommRing k] [AddCommGroup M]
    [Module (VariableRing k σ) M] (x : σ) : M →ₗ[VariableRing k σ] M :=
  LinearMap.lsmul (VariableRing k σ) M (MvPolynomial.X x)

theorem variableOperator_comm (k σ M : Type*) [CommRing k] [AddCommGroup M]
    [Module (VariableRing k σ) M] (x y : σ) (m : M) :
    variableOperator k σ M x (variableOperator k σ M y m) =
      variableOperator k σ M y (variableOperator k σ M x m) := smul_comm _ _ _

end NSP14.Homological

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

def AtomExponent := {a : S.carrier // S.IsAtom a.val}

noncomputable def atomExponentEquivAtoms : S.AtomExponent ≃ ↥S.atoms where
  toFun a := ⟨a.val.val,(S.mem_atoms_iff _).2 a.property⟩
  invFun a := ⟨⟨a.val,S.atoms_mem a.property⟩,(S.mem_atoms_iff _).1 a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance atomExponentFintype : Fintype S.AtomExponent :=
  Fintype.ofEquiv ↥S.atoms S.atomExponentEquivAtoms.symm

theorem atomExponent_card : Fintype.card S.AtomExponent=S.embeddingDimension := by
  rw [Fintype.card_congr S.atomExponentEquivAtoms,Fintype.card_coe]
  rfl

noncomputable def atomDegreeExponentEquiv : S.AtomExponent ≃ S.DegreeExponent 1 where
  toFun a := ⟨a.val,S.atom_order a.property⟩
  invFun a := ⟨a.val,(S.order_one_iff_atom a.val.property).1 a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (k : Type*) [CommRing k]

/-- The full e-variable source presentation; not the (e−1)-variable S₀. -/
abbrev FullPolynomialRing := NSP14.Homological.VariableRing k S.AtomExponent

noncomputable def fullPolynomialToG : S.FullPolynomialRing k →ₐ[k] S.TangentAlgebra k :=
  MvPolynomial.aeval (fun a => S.initialMonomial k a.val)

noncomputable instance fullPolynomialAlgebraG : Algebra (S.FullPolynomialRing k) (S.TangentAlgebra k) :=
  (S.fullPolynomialToG k).toRingHom.toAlgebra

noncomputable instance fullPolynomialScalarTowerG : IsScalarTower k (S.FullPolynomialRing k) (S.TangentAlgebra k) :=
  IsScalarTower.of_algebraMap_eq (fun c => (S.fullPolynomialToG k).commutes c |>.symm)

theorem fullPolynomialToG_X (a : S.AtomExponent) :
    S.fullPolynomialToG k (MvPolynomial.X a)=S.initialMonomial k a.val := MvPolynomial.aeval_X _ a

noncomputable def allAtomSubalgebra : Subalgebra k (S.TangentAlgebra k) :=
  Algebra.adjoin k (Set.range (fun a : S.AtomExponent => S.initialMonomial k a.val))

theorem initialMonomial_mem_allAtomSubalgebra (x : S.carrier) :
    S.initialMonomial k x ∈ S.allAtomSubalgebra k := by
  have gen : ∀ n, ∀ hn : n∈S, S.initialMonomial k ⟨n,hn⟩ ∈ S.allAtomSubalgebra k := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      let z : S.carrier := ⟨n,hn⟩
      by_cases hz : n=0
      · subst n
        change S.initialMonomial k 0 ∈ _
        rw [S.initialMonomial_zero]
        exact (S.allAtomSubalgebra k).one_mem
      · obtain ⟨a,v,ha,he,hl⟩ := S.atomic_live_split z (by change 0<n; omega)
        have hv : v.val<n := by
          have hh := congrArg Subtype.val he
          have hp := ha.2.1
          change n=a.val+v.val at hh
          omega
        have ham : S.initialMonomial k a ∈ S.allAtomSubalgebra k :=
          Algebra.subset_adjoin ⟨(⟨a,ha⟩ : S.AtomExponent),rfl⟩
        have hp := (S.allAtomSubalgebra k).mul_mem ham (ih v.val hv v.property)
        rw [S.initialMonomial_mul_live k a v hl] at hp
        exact (congrArg (S.initialMonomial k) he).symm ▸ hp
  exact gen x.val x.property

theorem allAtom_adjoin_top : S.allAtomSubalgebra k=⊤ := by
  apply top_unique
  intro a _
  rw [← S.tangent_expansion k a,Finsupp.sum]
  apply (S.allAtomSubalgebra k).sum_mem
  intro t _
  apply (S.allAtomSubalgebra k).smul_mem
  exact S.initialMonomial_mem_allAtomSubalgebra k t

theorem fullPolynomialToG_surjective : Function.Surjective (S.fullPolynomialToG k) := by
  have hr : (S.fullPolynomialToG k).range=⊤ := by
    rw [fullPolynomialToG,← Algebra.adjoin_range_eq_range_aeval]
    exact S.allAtom_adjoin_top k
  intro a
  have ha : a∈(S.fullPolynomialToG k).range := by rw [hr]; trivial
  exact ha

/-- Degree-one coordinates of the full presentation are exactly the actual atoms. -/
noncomputable def atomDegreeOneEquiv : (S.AtomExponent →₀ k) ≃ₗ[k] S.tangentDegree k 1 :=
  (Finsupp.domLCongr S.atomDegreeExponentEquiv).trans
    ((S.gradedPieceEquiv k 1).symm.trans
      (LinearEquiv.ofInjective (DirectSum.lof k ℕ (S.GradedPiece k) 1)
        (DirectSum.of_injective (β := S.GradedPiece k) 1)))

noncomputable def atomLinearForm : (S.AtomExponent →₀ k) →ₗ[k] S.FullPolynomialRing k :=
  Finsupp.linearCombination k (fun a => MvPolynomial.X a)

theorem atom_initial_linearIndependent : LinearIndependent k (fun a : S.AtomExponent => S.initialMonomial k a.val) := by
  have h := (S.tangentBasis k).linearIndependent.comp (fun a : S.AtomExponent => a.val) Subtype.val_injective
  change LinearIndependent k (fun a : S.AtomExponent => S.tangentBasis k a.val) at h
  have he : (fun a : S.AtomExponent => S.tangentBasis k a.val) =
      (fun a : S.AtomExponent => S.initialMonomial k a.val) :=
    funext (fun a => S.tangentBasis_eq_initial k a.val)
  rw [he] at h
  exact h

theorem fullPolynomialToG_linearForm (f : S.AtomExponent →₀ k) :
    S.fullPolynomialToG k (S.atomLinearForm k f) =
      Finsupp.linearCombination k (fun a : S.AtomExponent => S.initialMonomial k a.val) f := by
  have he : (S.fullPolynomialToG k).toLinearMap.comp (S.atomLinearForm k) =
      Finsupp.linearCombination k (fun a : S.AtomExponent => S.initialMonomial k a.val) := by
    apply Finsupp.basisSingleOne.ext
    intro a
    simp [atomLinearForm,S.fullPolynomialToG_X]
  exact LinearMap.congr_fun he f

/-- No extra linear relation in the e-variable presentation. -/
theorem fullPolynomialToG_linearForm_eq_zero_iff (f : S.AtomExponent →₀ k) :
    S.fullPolynomialToG k (S.atomLinearForm k f)=0 ↔ f=0 := by
  rw [S.fullPolynomialToG_linearForm]
  exact map_eq_zero_iff _ (S.atom_initial_linearIndependent k).finsuppLinearCombination_injective

noncomputable def fullPolynomialToFormalG : S.FullPolynomialRing k →ₐ[k] S.FormalTangentAlgebra k :=
  (S.completedGradedAlgEquiv k).toAlgHom.comp (S.fullPolynomialToG k)

noncomputable instance fullPolynomialAlgebraFormalG : Algebra (S.FullPolynomialRing k) (S.FormalTangentAlgebra k) :=
  (S.fullPolynomialToFormalG k).toRingHom.toAlgebra

noncomputable def completedPolynomialLinearEquiv :
    S.TangentAlgebra k ≃ₗ[S.FullPolynomialRing k] S.FormalTangentAlgebra k where
  toEquiv := (S.completedGradedAlgEquiv k).toEquiv
  map_add' := (S.completedGradedAlgEquiv k).map_add
  map_smul' p a := by
    change S.completedGradedAlgEquiv k (S.fullPolynomialToG k p*a) =
      S.completedGradedAlgEquiv k (S.fullPolynomialToG k p)*S.completedGradedAlgEquiv k a
    exact map_mul _ _ _

end NSP14.NumericalSemigroup
