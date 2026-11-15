module
public import NSP14.Endpoint.ArtinGradedMaps
public import NSP14.Lex.Hilbert
public import NSP14.Homological.GradedKoszulBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))

noncomputable def artinMonomialBasis : Module.Basis (StandardExponent MonomialOrder.degLex I) k
    (coefficientModule k (Fin q) (artinModule k (Fin q) I)) :=
  Finsupp.basisSingleOne.map (artinCoordinates k (Fin q) I).symm

theorem artinMonomialBasis_apply (p : StandardExponent MonomialOrder.degLex I) :
    artinMonomialBasis k q I p=Ideal.Quotient.mk I (MvPolynomial.monomial p.val 1) := by
  change (artinCoordinates k (Fin q) I).symm (Finsupp.single p 1)=_
  exact artinCoordinates_single k (Fin q) I p

theorem artinMonomialBasis_repr (a : coefficientModule k (Fin q) (artinModule k (Fin q) I))
    (p : StandardExponent MonomialOrder.degLex I) :
    (artinMonomialBasis k q I).repr a p=artinCoordinates k (Fin q) I a p := by
  rfl

abbrev ArtinChainIndex (t : ℤ) (i : ℕ) :=
  {a : KoszulSlot (variableList k (Fin q)).length i × StandardExponent MonomialOrder.degLex I //
    (a.2.val.degree:ℤ)=t-(i:ℤ)}

noncomputable instance artinChainIndex_finite (t : ℤ) (i : ℕ) : Finite (ArtinChainIndex k q I t i) := by
  let : Finite {p : StandardExponent MonomialOrder.degLex I // (p.val.degree:ℤ)=t-(i:ℤ)} :=
    Lex.standard_degree_finite k q I (t-(i:ℤ))
  let f : ArtinChainIndex k q I t i →
      KoszulSlot (variableList k (Fin q)).length i ×
        {p : StandardExponent MonomialOrder.degLex I // (p.val.degree:ℤ)=t-(i:ℤ)} :=
    fun a => (a.val.1,⟨a.val.2,a.property⟩)
  apply Finite.of_injective f
  intro a b he
  apply Subtype.ext
  have h : a.val.1=b.val.1 ∧ a.val.2=b.val.2 := by
    simpa only [f,Prod.mk.injEq,Subtype.mk.injEq] using he
  exact Prod.ext h.1 h.2

variable (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
include hI in
theorem artinMonomialBasis_homogeneous (p : StandardExponent MonomialOrder.degLex I) :
    artinMonomialBasis k q I p ∈ (artinGrading k (Fin q) I hI).degreeSpace (p.val.degree:ℤ) := by
  rw [artinMonomialBasis_apply]
  exact artin_mk_homogeneous k (Fin q) I hI p.val.degree _ (MvPolynomial.isHomogeneous_monomial (1:k) rfl)

noncomputable abbrev artinGradedChainSpace (t : ℤ) (i : ℕ) :=
  gradedKoszulSpace k (Fin q) (artinModule k (Fin q) I) (artinGrading k (Fin q) I hI)
    (variableList k (Fin q)) t i

noncomputable def artinGradedChainBasis (t : ℤ) (i : ℕ) :
    Module.Basis (ArtinChainIndex k q I t i) k (artinGradedChainSpace k q I hI t i) :=
  gradedKoszulSpaceBasis k (Fin q) (artinModule k (Fin q) I) (artinGrading k (Fin q) I hI)
    (artinMonomialBasis k q I) (fun p => (p.val.degree:ℤ)) (artinMonomialBasis_homogeneous k q I hI)
    (variableList k (Fin q)) t i

include hI in
theorem artinGradedChain_finite (t : ℤ) (i : ℕ) :
    Module.Finite k (artinGradedChainSpace k q I hI t i) := by
  let : Fintype (ArtinChainIndex k q I t i) := Fintype.ofFinite _
  exact Module.Finite.of_basis (artinGradedChainBasis k q I hI t i)

include hI in
theorem artinGradedChainBasis_inclusion (t : ℤ) (i : ℕ) (a : ArtinChainIndex k q I t i) :
    (artinGradedChainBasis k q I hI t i a).val=
      koszulSlotBasis k (Fin q) (artinModule k (Fin q) I) (artinMonomialBasis k q I)
        (variableList k (Fin q)) i a.val :=
  gradedKoszulSpaceBasis_inclusion k (Fin q) (artinModule k (Fin q) I) (artinGrading k (Fin q) I hI)
    (artinMonomialBasis k q I) (fun p => (p.val.degree:ℤ)) (artinMonomialBasis_homogeneous k q I hI)
    (variableList k (Fin q)) t i a

include hI in
theorem artinGradedChainBasis_repr (t : ℤ) (i : ℕ) (x : artinGradedChainSpace k q I hI t i)
    (a : ArtinChainIndex k q I t i) :
    (artinGradedChainBasis k q I hI t i).repr x a=
      (koszulSlotBasis k (Fin q) (artinModule k (Fin q) I) (artinMonomialBasis k q I)
        (variableList k (Fin q)) i).repr x.val a.val :=
  gradedKoszulSpaceBasis_repr k (Fin q) (artinModule k (Fin q) I) (artinGrading k (Fin q) I hI)
    (artinMonomialBasis k q I) (fun p => (p.val.degree:ℤ)) (artinMonomialBasis_homogeneous k q I hI)
    (variableList k (Fin q)) t i x a
include hI in
theorem artinGradedChainBasis_slot (t : ℤ) (i : ℕ) (a : ArtinChainIndex k q I t i) :
    (artinGradedChainBasis k q I hI t i a).val=
      coefficientSlotIn k (Fin q) (artinModule k (Fin q) I) (variableList k (Fin q)) i a.val.1
        (artinMonomialBasis k q I a.val.2) := by
  rw [artinGradedChainBasis_inclusion,koszulSlotBasis_apply]

include hI in
/-- An entry of the actual internal-degree differential is the actual signed
variable action in the original quotient's standard monomial coordinates. -/
theorem artinGradedBoundary_entry (t : ℤ) (i : ℕ)
    (s : ArtinChainIndex k q I t (i+1)) (r : ArtinChainIndex k q I t i) :
    (artinGradedChainBasis k q I hI t i).repr
      (gradedKoszulDifferential k (Fin q) (artinModule k (Fin q) I) (artinGrading k (Fin q) I hI)
        (variableList k (Fin q)) t i (artinGradedChainBasis k q I hI t (i+1) s)) r=
      artinCoordinates k (Fin q) I
        ((koszulSignedVariable k (Fin q) (artinModule k (Fin q) I)
          (koszulSlotArrow (variableList k (Fin q)) i s.val.1 r.val.1)).hom
            (artinMonomialBasis k q I s.val.2)) r.val.2 := by
  rw [artinGradedChainBasis_repr,koszulSlotBasis_repr]
  change (artinMonomialBasis k q I).repr
    (coefficientSlotOut k (Fin q) (artinModule k (Fin q) I) (variableList k (Fin q)) i r.val.1
      ((((coefficientKoszulListFunctor k (Fin q) (variableList k (Fin q))).obj (artinModule k (Fin q) I)).d
        (i+1) i (artinGradedChainBasis k q I hI t (i+1) s).val))) r.val.2=_
  rw [artinGradedChainBasis_slot,coefficientSlot_d_arrow,artinMonomialBasis_repr]
end NSP14.Endpoint
