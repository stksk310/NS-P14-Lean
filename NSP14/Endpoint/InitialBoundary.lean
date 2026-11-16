module
public import NSP14.Endpoint.ArtinGradedChain
public import NSP14.Endpoint.InitialAction
public import NSP14.Homological.WedgeExponent
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open NSP14.Homological
attribute [local instance] MvPolynomial.gradedAlgebra
namespace NSP14.Endpoint
variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))

noncomputable def artinChainTerm (t : ℤ) (i : ℕ) (a : ArtinChainIndex k q I t i) : Fin q →₀ ℕ :=
  a.val.2.val+wedgeExponent (koszulSlotWedge (variableList k (Fin q)) i a.val.1)

variable (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
include hI in
/-- The actual internal-degree Koszul matrix is upper triangular in
its augmented standard exponent, over every field. -/
theorem artinGradedBoundary_triangular (t : ℤ) (i : ℕ)
    (s : ArtinChainIndex k q I t (i+1)) (r : ArtinChainIndex k q I t i)
    (hlt : MonomialOrder.degLex.toSyn (artinChainTerm k q I t (i+1) s) <
      MonomialOrder.degLex.toSyn (artinChainTerm k q I t i r)) :
    (artinGradedChainBasis k q I hI t i).repr
      (gradedKoszulDifferential k (Fin q) (artinModule k (Fin q) I) (artinGrading k (Fin q) I hI)
        (variableList k (Fin q)) t i (artinGradedChainBasis k q I hI t (i+1) s)) r=0 := by
  rw [artinGradedBoundary_entry]
  cases he : koszulSlotArrow (variableList k (Fin q)) i s.val.1 r.val.1 with
  | none => simp [koszulSignedVariable]
  | some z =>
    rcases z with ⟨x,sign⟩
    have hw := koszulSlotArrow_exponent (variableList k (Fin q)) (variableList_nodup k (Fin q)) i
      s.val.1 r.val.1 he
    have hexp : s.val.2.val+wedgeExponent (koszulSlotWedge (variableList k (Fin q)) (i+1) s.val.1)=
        (s.val.2.val+Finsupp.single x 1)+wedgeExponent (koszulSlotWedge (variableList k (Fin q)) i r.val.1) := by
      rw [←hw]
      abel
    change MonomialOrder.degLex.toSyn (s.val.2.val+wedgeExponent
        (koszulSlotWedge (variableList k (Fin q)) (i+1) s.val.1)) <
      MonomialOrder.degLex.toSyn (r.val.2.val+wedgeExponent
        (koszulSlotWedge (variableList k (Fin q)) i r.val.1)) at hlt
    rw [hexp] at hlt
    have hp : MonomialOrder.degLex.toSyn (s.val.2.val+Finsupp.single x 1) <
        MonomialOrder.degLex.toSyn r.val.2.val := by
      apply (add_lt_add_iff_right (MonomialOrder.degLex.toSyn
        (wedgeExponent (koszulSlotWedge (variableList k (Fin q)) i r.val.1)))).mp
      simpa only [map_add] using hlt
    have hc := artin_variable_triangular k q I x s.val.2 r.val.2 hp
    cases sign <;> simpa [koszulSignedVariable,artinMonomialBasis] using hc
def koszulArrowEntry (o : Option (Fin q × Bool)) : k :=
  match o with
  | none => 0
  | some (_,false) => 1
  | some (_,true) => -1

include hI in
/-- Every same-augmented-term component is its actual signed incidence
scalar, independently of the homogeneous ideal. -/
theorem artinGradedBoundary_sameTerm (t : ℤ) (i : ℕ)
    (s : ArtinChainIndex k q I t (i+1)) (r : ArtinChainIndex k q I t i)
    (hsame : artinChainTerm k q I t (i+1) s=artinChainTerm k q I t i r) :
    (artinGradedChainBasis k q I hI t i).repr
      (gradedKoszulDifferential k (Fin q) (artinModule k (Fin q) I) (artinGrading k (Fin q) I hI)
        (variableList k (Fin q)) t i (artinGradedChainBasis k q I hI t (i+1) s)) r=
      koszulArrowEntry k q (koszulSlotArrow (variableList k (Fin q)) i s.val.1 r.val.1) := by
  rw [artinGradedBoundary_entry]
  cases he : koszulSlotArrow (variableList k (Fin q)) i s.val.1 r.val.1 with
  | none => simp [koszulSignedVariable,koszulArrowEntry]
  | some z =>
    rcases z with ⟨x,sign⟩
    have hw := koszulSlotArrow_exponent (variableList k (Fin q)) (variableList_nodup k (Fin q)) i
      s.val.1 r.val.1 he
    have hp : s.val.2.val+Finsupp.single x 1=r.val.2.val := by
      have ht : (s.val.2.val+Finsupp.single x 1)+
          wedgeExponent (koszulSlotWedge (variableList k (Fin q)) i r.val.1)=
          r.val.2.val+wedgeExponent (koszulSlotWedge (variableList k (Fin q)) i r.val.1) := by
        change s.val.2.val+wedgeExponent (koszulSlotWedge (variableList k (Fin q)) (i+1) s.val.1)=
          r.val.2.val+wedgeExponent (koszulSlotWedge (variableList k (Fin q)) i r.val.1) at hsame
        rw [←hw] at hsame
        simpa only [add_assoc,add_comm,add_left_comm] using hsame
      exact add_right_cancel ht
    have hstd : s.val.2.val+Finsupp.single x 1 ∈ StandardExponent MonomialOrder.degLex I := by
      rw [hp]
      exact r.val.2.property
    have hc : artinCoordinates k (Fin q) I ((MvPolynomial.X x : VariableRing k (Fin q)) •
        (artinCoordinates k (Fin q) I).symm (Finsupp.single s.val.2 1)) r.val.2=1 := by
      rw [artin_variable_standard k q I x s.val.2 r.val.2 hstd,ite_eq_left hp]
    cases sign <;> simpa [koszulSignedVariable,artinMonomialBasis,koszulArrowEntry] using hc

include hI in
/-- An actual monomial quotient's internal-degree differential preserves
augmented exponent exactly; its other ordered blocks are zero. -/
theorem artinGradedBoundary_monomial_offTerm (hM : Lex.IsMonomial k q I) (t : ℤ) (i : ℕ)
    (s : ArtinChainIndex k q I t (i+1)) (r : ArtinChainIndex k q I t i)
    (hne : artinChainTerm k q I t (i+1) s ≠ artinChainTerm k q I t i r) :
    (artinGradedChainBasis k q I hI t i).repr
      (gradedKoszulDifferential k (Fin q) (artinModule k (Fin q) I) (artinGrading k (Fin q) I hI)
        (variableList k (Fin q)) t i (artinGradedChainBasis k q I hI t (i+1) s)) r=0 := by
  rw [artinGradedBoundary_entry]
  cases he : koszulSlotArrow (variableList k (Fin q)) i s.val.1 r.val.1 with
  | none => simp [koszulSignedVariable]
  | some z =>
    rcases z with ⟨x,sign⟩
    have hw := koszulSlotArrow_exponent (variableList k (Fin q)) (variableList_nodup k (Fin q)) i
      s.val.1 r.val.1 he
    have hp : s.val.2.val+Finsupp.single x 1 ≠ r.val.2.val := by
      intro heq
      apply hne
      change s.val.2.val+wedgeExponent (koszulSlotWedge (variableList k (Fin q)) (i+1) s.val.1)=
        r.val.2.val+wedgeExponent (koszulSlotWedge (variableList k (Fin q)) i r.val.1)
      rw [←hw,←heq]
      abel
    have hc : artinCoordinates k (Fin q) I ((MvPolynomial.X x : VariableRing k (Fin q)) •
        (artinCoordinates k (Fin q) I).symm (Finsupp.single s.val.2 1)) r.val.2=0 := by
      rw [artin_variable_monomial k q I hM x s.val.2 r.val.2,ite_eq_right hp]
    cases sign <;> simpa [koszulSignedVariable,artinMonomialBasis] using hc
end NSP14.Endpoint
