module
public import NSP14.Width.AntipodalPresentation
public import NSP14.Endpoint.StandardArtinGrading
public import NSP14.Width.BinaryMonomialPower
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data) (k : Type) [Field k] (h t : ℕ) (ha : D.a={t,h,t+h})
local notation "Y" => D.antipodalVariable h t ha 0
local notation "Z" => D.antipodalVariable h t ha 1
local notation "W" => D.antipodalVariable h t ha 2

noncomputable def antipodalQuadraticIdeal : Ideal (D.InternalRing k) :=
  Ideal.span ((fun β : D.a →₀ ℕ => MvPolynomial.monomial β (1:k)) ''
    {Finsupp.single Y 1+Finsupp.single Z 1,Finsupp.single Z 2,Finsupp.single Z 1+Finsupp.single W 1})

/-- The literal ideal from the requested actual antipodal presentation. -/
noncomputable def antipodalPresentationIdeal : Ideal (D.InternalRing k) :=
  Ideal.span ({MvPolynomial.X Y*MvPolynomial.X Z,(MvPolynomial.X Z)^2,MvPolynomial.X Z*MvPolynomial.X W} : Set (D.InternalRing k)) ⊔
    (Ideal.span ({MvPolynomial.X Y,MvPolynomial.X W} : Set (D.InternalRing k)))^h

theorem antipodalQuadraticIdeal_eq : D.antipodalQuadraticIdeal k h t ha=
    Ideal.span ({MvPolynomial.X Y*MvPolynomial.X Z,(MvPolynomial.X Z)^2,MvPolynomial.X Z*MvPolynomial.X W} : Set (D.InternalRing k)) := by
  unfold antipodalQuadraticIdeal
  rw [Set.image_insert_eq,Set.image_insert_eq,Set.image_singleton]
  simp only [pow_two,MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul,←Finsupp.single_add]

/-- The coefficientwise kernel ideal equals (yz,z²,zw)+(y,w)^h,
with all variables mapped to their actual original internal offsets. -/
theorem antipodalMonomialIdeal_eq (_hh : 4 ≤ h) (ht0 : 0<t) (ht : t<h) :
    D.antipodalMonomialIdeal k h t ha=D.antipodalPresentationIdeal k h t ha := by
  have hyz : Y≠Z := (D.antipodalVariableEquiv h t ht0 ht ha).injective.ne (by decide : (0:Fin 3)≠1)
  have hyw : Y≠W := (D.antipodalVariableEquiv h t ht0 ht ha).injective.ne (by decide : (0:Fin 3)≠2)
  have hzw : Z≠W := (D.antipodalVariableEquiv h t ht0 ht ha).injective.ne (by decide : (1:Fin 3)≠2)
  rw [antipodalPresentationIdeal,←D.antipodalQuadraticIdeal_eq k h t ha,
    ←NSP14.Width.binaryCutoffIdeal_eq_power k Y W hyw h]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨β,hβ,rfl⟩
    by_cases htr : h ≤ β Y+β W
    · apply Ideal.mem_sup_right
      exact Ideal.subset_span ⟨β,htr,rfl⟩
    · apply Ideal.mem_sup_left
      apply MvPolynomial.mem_ideal_span_monomial_image.mpr
      intro γ hγ
      have he : γ=β := by simpa only [MvPolynomial.support_monomial,one_ne_zero,ite_false,Finset.mem_singleton] using hγ
      subst γ
      have hb : 1 ≤ β Z := by
        by_contra hn
        apply hβ
        left
        exact ⟨by omega,by omega⟩
      by_cases hy : 1 ≤ β Y
      · refine ⟨Finsupp.single Y 1+Finsupp.single Z 1,by simp,?_⟩
        intro b
        by_cases hby : b=Y
        · subst b
          simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hyz,add_zero]
          exact hy
        by_cases hbz : b=Z
        · subst b
          simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hyz.symm,zero_add]
          exact hb
        · simp [Finsupp.add_apply,Finsupp.single_eq_of_ne hby,Finsupp.single_eq_of_ne hbz]
      by_cases hw : 1 ≤ β W
      · refine ⟨Finsupp.single Z 1+Finsupp.single W 1,by simp,?_⟩
        intro b
        by_cases hbz : b=Z
        · subst b
          simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hzw,add_zero]
          exact hb
        by_cases hbw : b=W
        · subst b
          simp only [Finsupp.add_apply,Finsupp.single_eq_same,Finsupp.single_eq_of_ne hzw.symm,zero_add]
          exact hw
        · simp [Finsupp.add_apply,Finsupp.single_eq_of_ne hbz,Finsupp.single_eq_of_ne hbw]
      have hb2 : 2 ≤ β Z := by
        by_contra hn
        apply hβ
        right
        exact ⟨by omega,by omega,by omega⟩
      exact ⟨Finsupp.single Z 2,by simp,Finsupp.single_le_iff.mpr hb2⟩
  · apply sup_le
    · apply Ideal.span_le.mpr
      rintro _ ⟨β,hβ,rfl⟩
      apply Ideal.subset_span
      refine ⟨β,?_,rfl⟩
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hβ
      rcases hβ with rfl|rfl|rfl <;>
        simp [AntipodalStandard,hyz,hyz.symm,hyw,hyw.symm,hzw,hzw.symm]
    · apply Ideal.span_le.mpr
      rintro _ ⟨β,hβ,rfl⟩
      apply Ideal.subset_span
      refine ⟨β,?_,rfl⟩
      intro hs
      rcases hs with ⟨_,hs⟩|⟨hy,_,hw⟩ <;> change h ≤ β Y+β W at hβ <;> omega

/-- Actual QC is the specified quotient, using the original internal
polynomial ring and original coefficient field. -/
noncomputable def antipodalPresentation (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) :
    (D.InternalRing k ⧸ D.antipodalPresentationIdeal k h t ha) ≃ₐ[k] D.QCore k :=
  (Ideal.quotientEquivAlgOfEq k (D.antipodalMonomialIdeal_eq k h t ha hh ht0 ht).symm).trans
    (D.antipodalMonomialPresentation k h t hu hh ht0 ht hc ha)


/-- The isomorphism is induced by the original internal-to-QC map. -/
theorem antipodalPresentation_mk (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (f : D.InternalRing k) :
    D.antipodalPresentation k h t ha hu hh ht0 ht hc
      (Ideal.Quotient.mk _ f)=D.internalToQCore k f := by
  rfl

/-- In particular each original internal variable has its actual image. -/
theorem antipodalPresentation_variable (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (i : Fin 3) :
    D.antipodalPresentation k h t ha hu hh ht0 ht hc
      (Ideal.Quotient.mk _ (MvPolynomial.X (D.antipodalVariable h t ha i)))=
        Ideal.Quotient.mk _ (D.coreMonomial k
          (D.coreGeneratorPoint (D.internalVariable (D.antipodalVariable h t ha i)))) := by
  rw [D.antipodalPresentation_mk]
  change Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X _))=_
  rw [D.internalToCore_X]


attribute [local instance] MvPolynomial.gradedAlgebra
/-- The specified presentation ideal is homogeneous in the standard grading. -/
theorem antipodalPresentationIdeal_homogeneous (hh : 4 ≤ h) (ht0 : 0<t) (ht : t<h) :
    (D.antipodalPresentationIdeal k h t ha).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule D.a k) := by
  rw [←D.antipodalMonomialIdeal_eq k h t ha hh ht0 ht]
  apply Ideal.homogeneous_span
  rintro _ ⟨β,_,rfl⟩
  exact ⟨β.degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩

/-- The ring isomorphism also respects the actual polynomial action,
so it identifies the Tor problem rather than just algebra dimensions. -/
noncomputable def antipodalModuleIso (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) :
    NSP14.Endpoint.artinModule k D.a (D.antipodalPresentationIdeal k h t ha) ≅ D.QCoreModule k := by
  let e := D.antipodalPresentation k h t ha hu hh ht0 ht hc
  let f : NSP14.Endpoint.artinModule k D.a (D.antipodalPresentationIdeal k h t ha) →ₗ[D.InternalRing k]
      D.QCoreModule k := {
    toFun a := e a
    map_add' a b := e.map_add a b
    map_smul' r a := by
      change e (Ideal.Quotient.mk _ r*a)=D.internalToQCore k r*e a
      rw [map_mul]
      rfl }
  exact LinearEquiv.toModuleIso (LinearEquiv.ofBijective f e.bijective)

theorem antipodal_actual_betti (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (i : ℕ) :
    NSP14.Homological.totalBetti k D.a (D.QCoreModule k) i=
      NSP14.Homological.totalBetti k D.a
        (NSP14.Endpoint.artinModule k D.a (D.antipodalPresentationIdeal k h t ha)) i :=
  (NSP14.Homological.totalBetti_iso k D.a (D.antipodalModuleIso k h t ha hu hh ht0 ht hc) i).symm


/-- Every monomial keeps its standard degree under the actual algebra
presentation, as measured by the original QC grading coordinates. -/
theorem antipodalPresentation_monomial_degree (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (β : D.a →₀ ℕ)
    (p : D.CoreMinimalIndex) (hne : D.QCoreDegree p≠(β.degree:ℤ)) :
    D.QCoreCoordinates k (D.antipodalPresentation k h t ha hu hh ht0 ht hc
      (Ideal.Quotient.mk _ (MvPolynomial.monomial β (1:k)))) p=0 := by
  rw [D.antipodalPresentation_mk]
  change D.QCoreCoordinates k (Ideal.Quotient.mk _
    (D.internalToCore k (MvPolynomial.monomial β (1:k)))) p=0
  rw [D.internalToCore_monomial]
  change D.QCoreCoordinates k (Ideal.Quotient.mk _ (D.coreMonomial k (D.internalPoint β))) p=0
  rw [D.QCore_class_monomial]
  split_ifs with hm
  · rw [D.QCoreCoordinates_basis]
    apply Finsupp.single_eq_of_ne
    intro he
    subst p
    apply hne
    change (D.coreDegree (D.internalPoint β):ℤ)=(β.degree:ℤ)
    rw [D.internalPoint_degree,←Finsupp.degree_eq_sum]
  · rw [map_zero,Finsupp.zero_apply]
end NSP14.Endpoint.Data
