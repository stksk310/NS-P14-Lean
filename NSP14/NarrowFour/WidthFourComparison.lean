module
public import NSP14.NarrowFour.WidthFourInitial
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory NSP14.Homological
namespace NSP14.NarrowFour.WidthFour

theorem theta_six : (theta 6 0,theta 6 1,theta 6 2,theta 6 3,theta 6 6)=(2,2,1,1,0) := by decide

theorem theta_four_zero (Q : ℕ) (hQ : 2 ≤ Q) :
    theta (4*Q) 0=Q ∧ theta (4*Q) 1=Q ∧ theta (4*Q) 2=Q ∧
      theta (4*Q) 3=Q ∧ theta (4*Q) 6=Q-1 := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> unfold theta <;> rw [kappa_ceil] <;> push_cast <;> omega

theorem theta_four_one (Q : ℕ) (hQ : 2 ≤ Q) :
    theta (4*Q+1) 0=Q+1 ∧ theta (4*Q+1) 1=Q ∧ theta (4*Q+1) 2=Q ∧
      theta (4*Q+1) 3=Q ∧ theta (4*Q+1) 6=Q-1 := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> unfold theta <;> rw [kappa_ceil] <;> push_cast <;> omega

theorem theta_four_two (Q : ℕ) (hQ : 2 ≤ Q) :
    theta (4*Q+2) 0=Q+1 ∧ theta (4*Q+2) 1=Q+1 ∧ theta (4*Q+2) 2=Q ∧
      theta (4*Q+2) 3=Q ∧ theta (4*Q+2) 6=Q-1 := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> unfold theta <;> rw [kappa_ceil] <;> push_cast <;> omega

theorem theta_four_three (Q : ℕ) (hQ : 1 ≤ Q) :
    theta (4*Q+3) 0=Q+1 ∧ theta (4*Q+3) 1=Q+1 ∧ theta (4*Q+3) 2=Q+1 ∧
      theta (4*Q+3) 3=Q ∧ theta (4*Q+3) 6=Q := by
  refine ⟨?_,?_,?_,?_,?_⟩ <;> unfold theta <;> rw [kappa_ceil] <;> push_cast <;> omega

variable (D : Endpoint.Data) (k : Type) [Field k]

/-- The literal target's own actual first Betti row, for all m in the width-four family. -/
theorem target_first (hq : D.q=2) (hd : D.d=1) (hu : D.u=4) (hm : 6 ≤ D.m) :
    let he : 2 ≤ D.source.embeddingDimension := by rw [D.embeddingDimension,hq];omega
    totalBetti k (D.source.intervalCompletion he).AtomExponent
      (ModuleCat.of ((D.source.intervalCompletion he).FullPolynomialRing k)
        ((D.source.intervalCompletion he).FormalTangentAlgebra k)) 1=10-(D.m-1)%4 := by
  dsimp only
  rw [D.source.interval_completed_betti_profile k _ 1 (by omega)]
  have hv : (D.source.intervalAP (by rw [D.embeddingDimension,hq];omega)).v=4 := by
    change min D.source.width (D.source.multiplicity-1)=4
    rw [D.width,D.multiplicity,hd,hu,one_mul,min_eq_left (by omega)]
  have hA : (D.source.intervalAP (by rw [D.embeddingDimension,hq];omega)).m=D.m := D.multiplicity
  simp only [ArithmeticSequence.Data.positiveBettiProfile,
    ArithmeticSequence.Data.residueDefect,hv,hA]
  have hmod := Nat.mod_lt (D.m-1) (by omega : 0<4)
  split_ifs <;> norm_num [Nat.choose] <;> omega


noncomputable def actualModule (hu : D.u=4) (ha : D.a={1,3}) : ModuleCat (P k) :=
  polynomialRegularModule k (Fin 4) (D.source.TangentAlgebra k) (toActual D k hu ha)

noncomputable instance actualModule_finite (hu : D.u=4) (ha : D.a={1,3}) :
    Module.Finite (P k) (actualModule D k hu ha) :=
  regularPresentation_finite k (Fin 4) (D.source.TangentAlgebra k) (toActual D k hu ha)
    (toActual_surjective D k hu ha)

noncomputable def renamedModule (hu : D.u=4) (ha : D.a={1,3}) : ModuleCat (P k) :=
  (ModuleCat.restrictScalars (renameVariables D k hu ha).toRingEquiv.toRingHom).obj (D.fullG k)

noncomputable instance renamedModule_finite (hu : D.u=4) (ha : D.a={1,3}) :
    Module.Finite (P k) (renamedModule D k hu ha) :=
  polynomialEquivRestricted_finite k (Fin 4) D.Variables (renameVariables D k hu ha) (D.fullG k)

noncomputable def actualRenamedIso (hu : D.u=4) (ha : D.a={1,3}) :
    actualModule D k hu ha ≅ renamedModule D k hu ha := by
  let e : actualModule D k hu ha ≃ₗ[P k] renamedModule D k hu ha := {
    toFun a := a
    invFun a := a
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' r a := by
      change toActual D k hu ha r*(show D.source.TangentAlgebra k from a)=
        D.fullToG k ((renameVariables D k hu ha) r)*(show D.source.TangentAlgebra k from a)
      rw [toActual_full]
      rfl }
  exact e.toModuleIso

theorem actualModule_totalBetti (hu : D.u=4) (ha : D.a={1,3}) (i : ℕ) :
    totalBetti k (Fin 4) (actualModule D k hu ha) i=totalBetti k D.Variables (D.fullG k) i := by
  rw [totalBetti_iso k (Fin 4) (actualRenamedIso D k hu ha) i]
  exact (polynomialEquivBettiIso k (Fin 4) D.Variables (renameVariables D k hu ha)
    (augmentation_rename k (Fin 4) D.Variables (variableEquiv D hu ha)) (D.fullG k) i).toLinearEquiv.finrank_eq

theorem actualModule_completed (hu : D.u=4) (ha : D.a={1,3}) (i : ℕ) :
    totalBetti k (Fin 4) (actualModule D k hu ha) i=
      totalBetti k D.source.AtomExponent
        (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i := by
  rw [actualModule_totalBetti,D.fullG_totalBetti,D.source.completed_totalBetti k]

/-- The proved actual kernel presentation is paid through actual Tor1 and variable renaming. -/
theorem actual_first_le_family (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3})
    {ι : Type} [Fintype ι] (v : ι → P k) (hgen : candidateIdeal k D.m=Ideal.span (Set.range v)) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) 1 ≤ Fintype.card ι := by
  rw [←actualModule_completed D k hu ha 1]
  let : Module.Finite (P k) (polynomialRegularModule k (Fin 4) (D.source.TangentAlgebra k) (toActual D k hu ha)) :=
    actualModule_finite D k hu ha
  have e := NSP14.Endpoint.cyclicQuotientModuleIso k (Fin 4) (D.source.TangentAlgebra k)
    (toActual D k hu ha) (toActual_surjective D k hu ha)
  change totalBetti k (Fin 4) (polynomialRegularModule k (Fin 4) (D.source.TangentAlgebra k) (toActual D k hu ha)) 1 ≤ _
  rw [←totalBetti_iso k (Fin 4) e 1,actual_kernel_eq D k hm hd hu ha]
  exact first_le_generators k (candidateIdeal k D.m) (candidate_augmentation D k hm hd hu ha) v hgen
section Families
variable (k : Type) [Field k]

noncomputable def selectedFamily (m : ℕ) (C : Finset (Fin 4)) (T : Finset (Fin 5)) :
    ↑C ⊕ ↑T → P k := Sum.elim (fun i => coreRelation k i.val) (fun i => tailRelation k m i.val)

noncomputable def selectedIdeal (m : ℕ) (C : Finset (Fin 4)) (T : Finset (Fin 5)) : Ideal (P k) :=
  Ideal.span (Set.range (selectedFamily k m C T))

theorem core_mem_selected (m : ℕ) (C : Finset (Fin 4)) (T : Finset (Fin 5)) (i : Fin 4) (hi : i∈C) :
    coreRelation k i∈selectedIdeal k m C T := Ideal.subset_span ⟨Sum.inl ⟨i,hi⟩,rfl⟩
theorem tail_mem_selected (m : ℕ) (C : Finset (Fin 4)) (T : Finset (Fin 5)) (i : Fin 5) (hi : i∈T) :
    tailRelation k m i∈selectedIdeal k m C T := Ideal.subset_span ⟨Sum.inr ⟨i,hi⟩,rfl⟩

theorem selected_le_candidate (m : ℕ) (C : Finset (Fin 4)) (T : Finset (Fin 5)) :
    selectedIdeal k m C T ≤ candidateIdeal k m := by
  apply Ideal.span_le.mpr
  rintro f ⟨i,rfl⟩
  cases i with
  | inl i => exact Ideal.subset_span ⟨Sum.inl i.val,rfl⟩
  | inr i => exact Ideal.subset_span ⟨Sum.inr i.val,rfl⟩

theorem candidate_eq_selected (m : ℕ) (C : Finset (Fin 4)) (T : Finset (Fin 5))
    (hc : ∀ i : Fin 4,coreRelation k i∈selectedIdeal k m C T)
    (ht : ∀ i : Fin 5,tailRelation k m i∈selectedIdeal k m C T) :
    candidateIdeal k m=selectedIdeal k m C T := by
  apply le_antisymm _ (selected_le_candidate k m C T)
  apply Ideal.span_le.mpr
  rintro f ⟨i,rfl⟩
  cases i with
  | inl i => exact hc i
  | inr i => exact ht i

theorem tail_mem_of_le (m : ℕ) (I : Ideal (P k)) (i j : Fin 5)
    (hy : anchorY j ≤ anchorY i) (hz : anchorZ j ≤ anchorZ i)
    (hv : theta m (anchorN j) ≤ theta m (anchorN i)) (hj : tailRelation k m j∈I) :
    tailRelation k m i∈I := by
  have heY : anchorY i=anchorY i-anchorY j+anchorY j := (Nat.sub_add_cancel hy).symm
  have heZ : anchorZ i=anchorZ i-anchorZ j+anchorZ j := (Nat.sub_add_cancel hz).symm
  have heV : theta m (anchorN i)=theta m (anchorN i)-theta m (anchorN j)+theta m (anchorN j) :=
    (Nat.sub_add_cancel hv).symm
  have he : tailRelation k m i=
      (MvPolynomial.X 1^(anchorY i-anchorY j)*MvPolynomial.X 2^(anchorZ i-anchorZ j)*
        MvPolynomial.X 3^(theta m (anchorN i)-theta m (anchorN j)))*tailRelation k m j := by
    unfold tailRelation
    conv_lhs => rw [heY,heZ,heV,pow_add,pow_add,pow_add]
    ring
  rw [he]
  exact I.mul_mem_left _ hj

theorem four_cases (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by fin_cases i <;> decide
theorem five_cases (i : Fin 5) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by fin_cases i <;> decide

theorem candidate_reduced_zero (Q : ℕ) (hQ : 2 ≤ Q) :
    candidateIdeal k (4*Q)=selectedIdeal k (4*Q) Finset.univ {0,4} := by
  obtain ⟨h0,h1,h2,h3,h6⟩ := theta_four_zero Q hQ
  apply candidate_eq_selected k (4*Q) Finset.univ {0,4}
  · intro i
    exact core_mem_selected k (4*Q) Finset.univ {0,4} i (Finset.mem_univ _)
  · intro i
    rcases five_cases i with rfl|rfl|rfl|rfl|rfl
    · exact tail_mem_selected k (4*Q) Finset.univ {0,4} 0 (by decide)
    · exact tail_mem_of_le k (4*Q) (selectedIdeal k (4*Q) Finset.univ {0,4}) 1 0
        (by decide) (by decide) (by change theta (4*Q) 0 ≤ theta (4*Q) 1;omega)
        (tail_mem_selected k (4*Q) Finset.univ {0,4} 0 (by decide))
    · exact tail_mem_of_le k (4*Q) (selectedIdeal k (4*Q) Finset.univ {0,4}) 2 0
        (by decide) (by decide) (by change theta (4*Q) 0 ≤ theta (4*Q) 2;omega)
        (tail_mem_selected k (4*Q) Finset.univ {0,4} 0 (by decide))
    · exact tail_mem_of_le k (4*Q) (selectedIdeal k (4*Q) Finset.univ {0,4}) 3 0
        (by decide) (by decide) (by change theta (4*Q) 0 ≤ theta (4*Q) 3;omega)
        (tail_mem_selected k (4*Q) Finset.univ {0,4} 0 (by decide))
    · exact tail_mem_selected k (4*Q) Finset.univ {0,4} 4 (by decide)

theorem candidate_reduced_one (Q : ℕ) (hQ : 2 ≤ Q) :
    candidateIdeal k (4*Q+1)=selectedIdeal k (4*Q+1) Finset.univ {0,1,3,4} := by
  obtain ⟨h0,h1,h2,h3,h6⟩ := theta_four_one Q hQ
  apply candidate_eq_selected k (4*Q+1) Finset.univ {0,1,3,4}
  · intro i
    exact core_mem_selected k (4*Q+1) Finset.univ {0,1,3,4} i (Finset.mem_univ _)
  · intro i
    rcases five_cases i with rfl|rfl|rfl|rfl|rfl
    · exact tail_mem_selected k (4*Q+1) Finset.univ {0,1,3,4} 0 (by decide)
    · exact tail_mem_selected k (4*Q+1) Finset.univ {0,1,3,4} 1 (by decide)
    · exact tail_mem_of_le k (4*Q+1) (selectedIdeal k (4*Q+1) Finset.univ {0,1,3,4}) 2 1
        (by decide) (by decide) (by change theta (4*Q+1) 1 ≤ theta (4*Q+1) 2;omega)
        (tail_mem_selected k (4*Q+1) Finset.univ {0,1,3,4} 1 (by decide))
    · exact tail_mem_selected k (4*Q+1) Finset.univ {0,1,3,4} 3 (by decide)
    · exact tail_mem_selected k (4*Q+1) Finset.univ {0,1,3,4} 4 (by decide)

theorem candidate_reduced_two (Q : ℕ) (hQ : 2 ≤ Q) :
    candidateIdeal k (4*Q+2)=selectedIdeal k (4*Q+2) Finset.univ {0,2,3,4} := by
  obtain ⟨h0,h1,h2,h3,h6⟩ := theta_four_two Q hQ
  apply candidate_eq_selected k (4*Q+2) Finset.univ {0,2,3,4}
  · intro i
    exact core_mem_selected k (4*Q+2) Finset.univ {0,2,3,4} i (Finset.mem_univ _)
  · intro i
    rcases five_cases i with rfl|rfl|rfl|rfl|rfl
    · exact tail_mem_selected k (4*Q+2) Finset.univ {0,2,3,4} 0 (by decide)
    · exact tail_mem_of_le k (4*Q+2) (selectedIdeal k (4*Q+2) Finset.univ {0,2,3,4}) 1 0
        (by decide) (by decide) (by change theta (4*Q+2) 0 ≤ theta (4*Q+2) 1;omega)
        (tail_mem_selected k (4*Q+2) Finset.univ {0,2,3,4} 0 (by decide))
    · exact tail_mem_selected k (4*Q+2) Finset.univ {0,2,3,4} 2 (by decide)
    · exact tail_mem_selected k (4*Q+2) Finset.univ {0,2,3,4} 3 (by decide)
    · exact tail_mem_selected k (4*Q+2) Finset.univ {0,2,3,4} 4 (by decide)

theorem candidate_reduced_three (Q : ℕ) (hQ : 1 ≤ Q) :
    candidateIdeal k (4*Q+3)=selectedIdeal k (4*Q+3) Finset.univ {0,3} := by
  obtain ⟨h0,h1,h2,h3,h6⟩ := theta_four_three Q hQ
  apply candidate_eq_selected k (4*Q+3) Finset.univ {0,3}
  · intro i
    exact core_mem_selected k (4*Q+3) Finset.univ {0,3} i (Finset.mem_univ _)
  · intro i
    rcases five_cases i with rfl|rfl|rfl|rfl|rfl
    · exact tail_mem_selected k (4*Q+3) Finset.univ {0,3} 0 (by decide)
    · exact tail_mem_of_le k (4*Q+3) (selectedIdeal k (4*Q+3) Finset.univ {0,3}) 1 0
        (by decide) (by decide) (by change theta (4*Q+3) 0 ≤ theta (4*Q+3) 1;omega)
        (tail_mem_selected k (4*Q+3) Finset.univ {0,3} 0 (by decide))
    · exact tail_mem_of_le k (4*Q+3) (selectedIdeal k (4*Q+3) Finset.univ {0,3}) 2 0
        (by decide) (by decide) (by change theta (4*Q+3) 0 ≤ theta (4*Q+3) 2;omega)
        (tail_mem_selected k (4*Q+3) Finset.univ {0,3} 0 (by decide))
    · exact tail_mem_selected k (4*Q+3) Finset.univ {0,3} 3 (by decide)
    · exact tail_mem_of_le k (4*Q+3) (selectedIdeal k (4*Q+3) Finset.univ {0,3}) 4 3
        (by decide) (by decide) (by change theta (4*Q+3) 3 ≤ theta (4*Q+3) 6;omega)
        (tail_mem_selected k (4*Q+3) Finset.univ {0,3} 3 (by decide))

theorem candidate_reduced_six : candidateIdeal k 6=selectedIdeal k 6 {0,1} {0,2,3,4} := by
  have h0 : theta 6 0=2 := by decide
  have h1 : theta 6 1=2 := by decide
  have h2 : theta 6 2=1 := by decide
  have h6 : theta 6 6=0 := by decide
  let I := selectedIdeal k 6 {0,1} {0,2,3,4}
  have hz2 : tailRelation k 6 4∈I := tail_mem_selected k 6 {0,1} {0,2,3,4} 4 (by decide)
  have hv2 : tailRelation k 6 0∈I := tail_mem_selected k 6 {0,1} {0,2,3,4} 0 (by decide)
  have hy2v : tailRelation k 6 2∈I := tail_mem_selected k 6 {0,1} {0,2,3,4} 2 (by decide)
  apply candidate_eq_selected k 6 {0,1} {0,2,3,4}
  · intro i
    rcases four_cases i with rfl|rfl|rfl|rfl
    · exact core_mem_selected k 6 {0,1} {0,2,3,4} 0 (by decide)
    · exact core_mem_selected k 6 {0,1} {0,2,3,4} 1 (by decide)
    · have he : coreRelation k 2=MvPolynomial.X 0*tailRelation k 6 4-tailRelation k 6 2 := by
        simp [coreRelation,tailRelation,anchorY,anchorZ,anchorN,h2,h6]
      rw [he]
      exact I.sub_mem (I.mul_mem_left _ hz2) hy2v
    · have he : coreRelation k 3=MvPolynomial.X 2*tailRelation k 6 4-MvPolynomial.X 1*tailRelation k 6 0 := by
        simp [coreRelation,tailRelation,anchorY,anchorZ,anchorN,h0,h6];ring
      rw [he]
      exact I.sub_mem (I.mul_mem_left _ hz2) (I.mul_mem_left _ hv2)
  · intro i
    rcases five_cases i with rfl|rfl|rfl|rfl|rfl
    · exact hv2
    · exact tail_mem_of_le k 6 I 1 0 (by decide) (by decide)
        (by change theta 6 0 ≤ theta 6 1;omega) hv2
    · exact hy2v
    · exact tail_mem_selected k 6 {0,1} {0,2,3,4} 3 (by decide)
    · exact hz2
end Families

theorem first_le_selected (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3})
    (C : Finset (Fin 4)) (T : Finset (Fin 5)) (hgen : candidateIdeal k D.m=selectedIdeal k D.m C T) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) 1 ≤ C.card+T.card := by
  have h := actual_first_le_family D k hm hd hu ha (selectedFamily k D.m C T) hgen
  simpa only [Fintype.card_sum,Fintype.card_coe] using h

def generatorBound (m : ℕ) : ℕ := if m=6 then 6 else if m%4=0 ∨ m%4=3 then 6 else 8

theorem actual_first_bound (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) 1 ≤ generatorBound D.m := by
  by_cases h6 : D.m=6
  · have hgen : candidateIdeal k D.m=selectedIdeal k D.m {0,1} {0,2,3,4} := by
      rw [h6]
      exact candidate_reduced_six k
    have hb := first_le_selected D k hm hd hu ha {0,1} {0,2,3,4} hgen
    have hC : ({0,1} : Finset (Fin 4)).card=2 := by decide
    have hT : ({0,2,3,4} : Finset (Fin 5)).card=4 := by decide
    rw [hC,hT] at hb
    simpa only [generatorBound,h6,ite_true] using hb
  let Q := D.m/4
  have hmod := Nat.mod_add_div D.m 4
  have hmodlt := Nat.mod_lt D.m (by omega : 0<4)
  have hc : D.m%4=0 ∨ D.m%4=1 ∨ D.m%4=2 ∨ D.m%4=3 := by omega
  rcases hc with hρ|hρ|hρ|hρ
  · have heq : D.m=4*Q := by dsimp [Q];omega
    have hQ : 2 ≤ Q := by omega
    have hgen : candidateIdeal k D.m=selectedIdeal k D.m Finset.univ {0,4} := by
      rw [heq]
      exact candidate_reduced_zero k Q hQ
    have hb := first_le_selected D k hm hd hu ha Finset.univ {0,4} hgen
    have hC : (Finset.univ : Finset (Fin 4)).card=4 := by decide
    have hT : ({0,4} : Finset (Fin 5)).card=2 := by decide
    rw [hC,hT] at hb
    have hB : generatorBound D.m=6 := by simp [generatorBound,h6,hρ]
    rw [hB]
    exact hb
  · have heq : D.m=4*Q+1 := by dsimp [Q];omega
    have hQ : 2 ≤ Q := by omega
    have hgen : candidateIdeal k D.m=selectedIdeal k D.m Finset.univ {0,1,3,4} := by
      rw [heq]
      exact candidate_reduced_one k Q hQ
    have hb := first_le_selected D k hm hd hu ha Finset.univ {0,1,3,4} hgen
    have hC : (Finset.univ : Finset (Fin 4)).card=4 := by decide
    have hT : ({0,1,3,4} : Finset (Fin 5)).card=4 := by decide
    rw [hC,hT] at hb
    have hB : generatorBound D.m=8 := by simp [generatorBound,h6,hρ]
    rw [hB]
    exact hb
  · have heq : D.m=4*Q+2 := by dsimp [Q];omega
    have hQ : 2 ≤ Q := by omega
    have hgen : candidateIdeal k D.m=selectedIdeal k D.m Finset.univ {0,2,3,4} := by
      rw [heq]
      exact candidate_reduced_two k Q hQ
    have hb := first_le_selected D k hm hd hu ha Finset.univ {0,2,3,4} hgen
    have hC : (Finset.univ : Finset (Fin 4)).card=4 := by decide
    have hT : ({0,2,3,4} : Finset (Fin 5)).card=4 := by decide
    rw [hC,hT] at hb
    have hB : generatorBound D.m=8 := by simp [generatorBound,h6,hρ]
    rw [hB]
    exact hb
  · have heq : D.m=4*Q+3 := by dsimp [Q];omega
    have hQ : 1 ≤ Q := by omega
    have hgen : candidateIdeal k D.m=selectedIdeal k D.m Finset.univ {0,3} := by
      rw [heq]
      exact candidate_reduced_three k Q hQ
    have hb := first_le_selected D k hm hd hu ha Finset.univ {0,3} hgen
    have hC : (Finset.univ : Finset (Fin 4)).card=4 := by decide
    have hT : ({0,3} : Finset (Fin 5)).card=2 := by decide
    rw [hC,hT] at hb
    have hB : generatorBound D.m=6 := by simp [generatorBound,h6,hρ]
    rw [hB]
    exact hb

theorem generatorBound_payment (m : ℕ) (hm : 6 ≤ m) : generatorBound m ≤ 10-(m-1)%4 := by
  unfold generatorBound
  split_ifs <;> omega

theorem width_four_comparison (hq : D.q=2) (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) :
    let he : 2 ≤ D.source.embeddingDimension := by rw [D.embeddingDimension,hq];omega
    ∀ i : ℕ,totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i ≤
      totalBetti k (D.source.intervalCompletion he).AtomExponent
        (ModuleCat.of ((D.source.intervalCompletion he).FullPolynomialRing k)
          ((D.source.intervalCompletion he).FormalTangentAlgebra k)) i := by
  dsimp only
  intro i
  by_cases hi0 : i=0
  · subst i
    rw [D.source.completed_totalBetti_zero k,D.source.interval_completed_betti_zero k]
  by_cases hi1 : i=1
  · subst i
    rw [target_first D k hq hd hu hm]
    exact (actual_first_bound D k hm hd hu ha).trans (generatorBound_payment D.m hm)
  have he : D.source.embeddingDimension=4 := by rw [D.embeddingDimension,hq]
  have hw : D.source.width ≤ D.source.multiplicity-2 := by
    rw [D.width,D.multiplicity,hd,hu]
    omega
  exact narrow_four_higher D.source k he hw i (by omega)

end NSP14.NarrowFour.WidthFour
