module
public import NSP14.Lex.StableDegreeDecomposition
public import NSP14.Homological.GradedKoszulPieces
@[expose] public section
open scoped Classical BigOperators
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ) (I : Ideal (MvPolynomial (Fin q) k))
attribute [local instance] MvPolynomial.gradedAlgebra

theorem minimal_degree_sum_eq (d i : ℕ) :
    (∑ v∈(minimalGeneratorFinset k q I).filter (fun v => v.degree=d),
      (maxVariable q v-1).choose i)=
    ∑ α : MinimalDegreeMonomial k q I d,(maxVariable q α.val.val-1).choose i := by
  apply Finset.sum_bij (fun v hv =>
    (⟨⟨v,(Finset.mem_filter.mp hv).2⟩,(mem_minimalGeneratorFinset k q I v).mp (Finset.mem_filter.mp hv).1⟩ : MinimalDegreeMonomial k q I d))
  · intro v _; exact Finset.mem_univ _
  · intro a ha b hb he
    exact congrArg (fun z : MinimalDegreeMonomial k q I d => z.val.val) he
  · intro α _
    exact ⟨α.val.val,Finset.mem_filter.mpr ⟨(mem_minimalGeneratorFinset k q I _).mpr α.property,α.val.property⟩,rfl⟩
  · intro v _; rfl

theorem IsStronglyStable.graded_ek_degree (hI : IsStronglyStable k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (d i : ℕ) :
    quotientGradedBetti k q I hHom (i+1) ((d:ℤ)+(i:ℤ))=
      ∑ α : MinimalDegreeMonomial k q I d,(maxVariable q α.val.val-1).choose i := by
  rw [hI.graded_ek k q hproper hHom (minimalGeneratorFinset k q I) (mem_minimalGeneratorFinset k q I) (i+1) (by omega)]
  have hc (v : Fin q →₀ ℕ) : (v.degree:ℤ)+((i+1:ℕ):ℤ)-1=(d:ℤ)+(i:ℤ) ↔ v.degree=d := by omega
  simp_rw [hc,Nat.add_sub_cancel]
  rw [← Finset.sum_filter,minimal_degree_sum_eq]

end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

theorem quotientGradedBetti_top
    (hHom : (⊤ : Ideal (MvPolynomial (Fin q) k)).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (i : ℕ) (t : ℤ) : quotientGradedBetti k q ⊤ hHom i t=0 := by
  apply Nat.eq_zero_of_le_zero
  exact (gradedBetti_le_total k (Fin q) _ _ i t).trans_eq (totalBetti_eq_zero_of_subsingleton k (Fin q) _ i)

theorem quotientHilbert_zero_pos (I : Ideal (MvPolynomial (Fin q) k))
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hmono : IsMonomial k q I) (hproper : I≠⊤) : 0<quotientHilbert k q I hHom 0 := by
  rw [quotientHilbert_eq_standard_card]
  apply Fintype.card_pos_iff.mpr
  refine ⟨⟨⟨0,by simp⟩,?_⟩⟩
  rw [standardExponent_iff_not_mem k q hmono]
  intro hm
  apply hproper
  apply (Ideal.eq_top_iff_one I).mpr
  simpa only [MvPolynomial.monomial_zero',map_one] using hm

theorem quotientHilbert_top_zero
    (hHom : (⊤ : Ideal (MvPolynomial (Fin q) k)).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (d : ℕ) : quotientHilbert k q ⊤ hHom d=0 := by
  rw [quotientHilbert_eq_standard_card]
  let : IsEmpty {α : PolynomialDegreeIndex q d // α.val∈StandardExponent MonomialOrder.degLex (⊤ : Ideal (MvPolynomial (Fin q) k))} :=
    ⟨fun α => (standardExponent_iff_not_mem k q (I:=⊤) (by intro _ _ _ _; trivial) MonomialOrder.degLex _).mp α.property (by trivial)⟩
  exact Fintype.card_of_isEmpty

theorem IsStronglyStable.graded_betti_binomial_identity
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (d i : ℕ) :
    quotientGradedBetti k q I hHom (i+1) (((d+1:ℕ):ℤ)+(i:ℤ))+
      idealDegreeCard k q I d*q.choose (i+1)=
      degreeBinomialSum k q I (d+1) i+degreeBinomialSum k q I d (i+1) := by
  rw [hI.graded_ek_degree k q I hproper hHom]
  exact (hI.degree_binomial_identity k q I d i).symm

theorem IsStronglyStable.graded_betti_zero_below
    (I : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hproper : I≠⊤)
    (hHom : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k)) (i : ℕ) (t : ℤ) (ht : t≤(i:ℤ)) :
    quotientGradedBetti k q I hHom (i+1) t=0 := by
  rw [hI.graded_ek k q hproper hHom (minimalGeneratorFinset k q I) (mem_minimalGeneratorFinset k q I) (i+1) (by omega)]
  apply Finset.sum_eq_zero
  intro v hv
  have hn := minimalGenerator_ne_zero q k I hproper v ((mem_minimalGeneratorFinset k q I v).mp hv)
  have hd : v.degree≠0 := fun he => hn ((Finsupp.degree_eq_zero_iff v).mp he)
  rw [ite_eq_right (by omega)]

theorem IsStronglyStable.graded_betti_le_lex
    (I L : Ideal (MvPolynomial (Fin q) k)) (hI : IsStronglyStable k q I) (hL : IsLex k q L)
    (hHomI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hHomL : L.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin q) k))
    (hH : ∀ n,quotientHilbert k q I hHomI n=quotientHilbert k q L hHomL n)
    (i : ℕ) (hi : 1 ≤ i) (t : ℤ) : quotientGradedBetti k q I hHomI i t≤quotientGradedBetti k q L hHomL i t := by
  by_cases hproper : I=⊤
  · subst I
    rw [quotientGradedBetti_top]
    exact Nat.zero_le _
  have hproperL : L≠⊤ := by
    intro he
    have hp := quotientHilbert_zero_pos k q I hHomI hI.1 hproper
    have hh := hH 0
    have hz : quotientHilbert k q L hHomL 0=0 := by simpa only [he] using quotientHilbert_top_zero k q (he ▸ hHomL) 0
    omega
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i≠0)
  by_cases ht : t≤(j:ℤ)
  · rw [hI.graded_betti_zero_below k q I hproper hHomI j t ht]
    exact Nat.zero_le _
  let d : ℕ := (t-(j:ℤ)-1).toNat
  have ht' : t=((d+1:ℕ):ℤ)+(j:ℤ) := by dsimp [d]; omega
  rw [ht']
  have hci := idealDegreeCard_add_hilbert k q I hHomI hI.1 d
  have hcl := idealDegreeCard_add_hilbert k q L hHomL hL.1 d
  have hc : idealDegreeCard k q I d=idealDegreeCard k q L d := by have hh:=hH d; omega
  have hbI := hI.graded_betti_binomial_identity k q I hproper hHomI d j
  have hbL := IsStronglyStable.graded_betti_binomial_identity k q L
    ⟨hL.1,fun v hv a b hp hab => hL.raise k q v hv a b hp hab⟩ hproperL hHomL d j
  have hw1 := hI.binomial_degree_sum_le_lex_of_hilbert k q I L hL hHomI hHomL (d+1) j (hH (d+1))
  have hw0 := hI.binomial_degree_sum_le_lex_of_hilbert k q I L hL hHomI hHomL d (j+1) (hH d)
  rw [hc] at hbI
  simp only [Nat.succ_eq_add_one]
  omega
end NSP14.Lex

