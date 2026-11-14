module
public import NSP14.Width.FiveHoleKernel
public import NSP14.Homological.KoszulIndependentImages
public import NSP14.Homological.FiniteKoszulEulerAbove
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k]

theorem core_monomial_coordinate (p : D.corePoints) (j : D.CoreMinimalIndex) :
    D.QCoreCoordinates k (Ideal.Quotient.mk _ (D.coreMonomial k p)) j=
      if p=j.val then 1 else 0 := by
  by_cases hm : D.CoreMinimal p
  · rw [D.QCore_class_monomial,dite_eq_left hm,D.QCoreCoordinates_basis]
    simp only [Finsupp.single_apply]
    have he : (⟨p,hm⟩ : D.CoreMinimalIndex)=j ↔ p=j.val := by
      constructor
      · exact congrArg Subtype.val
      · intro he
        apply Subtype.ext
        exact he
    simp only [he]
  · rw [D.QCore_class_monomial,dite_eq_right hm,map_zero,Finsupp.zero_apply]
    have hn : p≠j.val := by intro he; apply hm; rw [he]; exact j.property
    rw [ite_eq_right hn]

noncomputable def coreColumn (p : D.corePoints) : coefficientModule k D.a (D.QCoreModule k) :=
  (D.QCoreCoefficientEquiv k).symm (Ideal.Quotient.mk _ (D.coreMonomial k p))
noncomputable def coreRow (j : D.CoreMinimalIndex) : coefficientModule k D.a (D.QCoreModule k) →ₗ[k] k :=
  (Finsupp.lapply j).comp (D.QCoreModuleCoordinates k).toLinearMap

theorem coreRow_variable_column (j : D.CoreMinimalIndex) (b : D.a) (p : D.corePoints) :
    D.coreRow k j ((MvPolynomial.X b : D.InternalRing k) • D.coreColumn k p)=
      if D.coreGeneratorPoint (D.internalVariable b)+p=j.val then 1 else 0 := by
  change D.QCoreCoordinates k (D.internalToQCore k (MvPolynomial.X b)*
    Ideal.Quotient.mk _ (D.coreMonomial k p)) j=_
  change D.QCoreCoordinates k (Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X b))*
    Ideal.Quotient.mk _ (D.coreMonomial k p)) j=_
  rw [←map_mul,D.internalToCore_X,D.coreMonomial_mul,D.core_monomial_coordinate]

/-- A 3×3 signed unit minor in the actual top differential. This uses
unit,x,y columns and coefficient x,x²,yz rows; it is valid in char 2. -/
theorem fiveHole_top_boundary_rank (hq : D.q=3) (hu : D.u=5) (flip : Bool)
    (v : Fin 3 ≃ D.a) (hv : ∀ i,(v i).val=fiveHoleValues flip i) :
    3 ≤ koszulBoundaryRank k D.a (D.QCoreModule k) 3 := by
  let M := D.QCoreModule k
  let xs := variableList k D.a
  have hslot : Nonempty (KoszulSlot xs.length 3) := Fintype.card_pos_iff.mp (by
    rw [koszulSlot_card,variableList_length,Fintype.card_coe]
    change 0<D.q.choose 3
    rw [hq]
    decide)
  let s : KoszulSlot xs.length 3 := Classical.choice hslot
  have hw : koszulSlotWedge xs 3 s=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [koszulSlotWedge_card xs (variableList_nodup k D.a),Finset.card_univ,Fintype.card_coe]
    change D.q ≤ 3
    omega
  have hdelete (b : D.a) := koszulSlot_delete_partner k D.a 2 s b (by rw [hw]; simp)
  let ds (b : D.a) : KoszulSlot xs.length 2 × Bool :=
    ((hdelete b).choose,(hdelete b).choose_spec.choose)
  have harrow (b : D.a) : koszulSlotArrow xs 2 s (ds b).1=some (b,(ds b).2) :=
    (hdelete b).choose_spec.choose_spec.2
  let vs : Fin 3 → D.a := ![v 0,v 0,v 2]
  let ps : Fin 3 → D.corePoints := ![0,D.coreGeneratorPoint (D.internalVariable (v 0)),D.coreGeneratorPoint (D.internalVariable (v 1))]
  let js : Fin 3 → D.CoreMinimalIndex :=
    ![D.internalMinimalIndex (v 0),⟨D.triplePoint v 2 0 0,D.fiveHole_two_survive hu flip v hv false⟩,
      ⟨D.triplePoint v 0 1 1,D.fiveHole_two_survive hu flip v hv true⟩]
  have heval (r c : Fin 3) : D.coreRow k (js r)
      ((MvPolynomial.X (vs r) : D.InternalRing k) • D.coreColumn k (ps c))=
        if r=c then 1 else 0 := by
    rw [D.coreRow_variable_column]
    have hcond : (D.coreGeneratorPoint (D.internalVariable (vs r))+ps c=(js r).val) ↔ r=c := by
      simp only [Subtype.ext_iff]
      fin_cases r <;> fin_cases c <;> cases flip <;>
        norm_num [vs,ps,js,triplePoint,internalMinimalIndex,coreGeneratorPoint,internalVariable,hv,fiveHoleValues]
    simp only [hcond]
  let columns (c : Fin 3) : (coefficientKoszulComplex k D.a M).X 3 :=
    coefficientSlotIn k D.a M xs 3 s (D.coreColumn k (ps c))
  let rows (r : Fin 3) : (coefficientKoszulComplex k D.a M).X 2 →ₗ[k] k :=
    (D.coreRow k (js r)).comp (coefficientSlotOut k D.a M xs 2 (ds (vs r)).1)
  let sign (r : Fin 3) : k := if (ds (vs r)).2 then -1 else 1
  have hentry (r c : Fin 3) : rows r (((coefficientKoszulComplex k D.a M).d 3 2).hom (columns c))=
      sign r*(if r=c then 1 else 0) := by
    change D.coreRow k (js r) (coefficientSlotOut k D.a M xs 2 (ds (vs r)).1
      (((coefficientKoszulComplex k D.a M).d 3 2).hom
        (coefficientSlotIn k D.a M xs 3 s (D.coreColumn k (ps c)))))=_
    have he := congrArg (D.coreRow k (js r))
      (coefficientSlot_d_arrow k D.a M xs 2 s (ds (vs r)).1 (D.coreColumn k (ps c)))
    change D.coreRow k (js r) (coefficientSlotOut k D.a M xs 2 (ds (vs r)).1
      (((coefficientKoszulComplex k D.a M).d 3 2).hom
        (coefficientSlotIn k D.a M xs 3 s (D.coreColumn k (ps c)))))=_ at he
    rw [he,harrow]
    cases hb : (ds (vs r)).2
    · change D.coreRow k (js r) ((MvPolynomial.X (vs r) : D.InternalRing k) • D.coreColumn k (ps c))=_
      rw [heval]
      by_cases hrc : r=c
      · subst c
        simp [sign,hb]
      · simp [sign,hb,hrc]
    · change D.coreRow k (js r) (-((MvPolynomial.X (vs r) : D.InternalRing k) • D.coreColumn k (ps c)))=_
      rw [map_neg,heval]
      by_cases hrc : r=c
      · subst c
        simp [sign,hb]
      · simp [sign,hb,hrc]
  let A : Matrix (Fin 3) (Fin 3) k := fun r c => rows r (((coefficientKoszulComplex k D.a M).d 3 2).hom (columns c))
  have hA : A=Matrix.diagonal sign := by
    ext r c
    rw [show A r c=sign r*(if r=c then 1 else 0) from hentry r c,Matrix.diagonal_apply]
    split_ifs <;> simp
  have hdet : Matrix.det A≠0 := by
    rw [hA,Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro r _
    dsimp [sign]
    split_ifs <;> simp
  let : Module.Finite k ((coefficientKoszulComplex k D.a M).X 2) :=
    koszul_chain_coefficient_finite k D.a xs M 2
  have h := functional_minor_rank_lower_bound k ((coefficientKoszulComplex k D.a M).d 3 2).hom columns rows hdet
  simpa only [Fintype.card_fin,koszulBoundaryRank,chainBoundaryRank_succ] using h

theorem fiveHole_third_add_three (hq : D.q=3) (hu : D.u=5) (flip : Bool)
    (v : Fin 3 ≃ D.a) (hv : ∀ i,(v i).val=fiveHoleValues flip i) :
    totalBetti k D.a (D.QCoreModule k) 3+3 ≤ D.coreP k := by
  have hr := D.fiveHole_top_boundary_rank k hq hu flip v hv
  have h := koszul_betti_chain_rank k D.a (D.QCoreModule k) 3
  rw [Fintype.card_coe,(D.QCoreCoefficientEquiv k).finrank_eq] at h
  change _=D.coreP k*D.q.choose 3 at h
  rw [hq] at h
  norm_num at h
  omega
end NSP14.Endpoint.Data
