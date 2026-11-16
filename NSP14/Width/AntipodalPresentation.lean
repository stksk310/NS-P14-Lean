module
public import NSP14.Width.AntipodalBasis
public import NSP14.Endpoint.TwoMonomial
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def antipodalVariable (h t : ℕ) (ha : D.a={t,h,t+h}) : Fin 3 → D.a :=
  ![⟨t,by rw [ha]; simp⟩,⟨h,by rw [ha]; simp⟩,⟨t+h,by rw [ha]; simp⟩]

noncomputable def antipodalVariableEquiv (h t : ℕ) (ht0 : 0<t) (ht : t<h)
    (ha : D.a={t,h,t+h}) : Fin 3 ≃ D.a :=
  Equiv.ofBijective (D.antipodalVariable h t ha) ⟨by
    intro i j he
    have hv := congrArg Subtype.val he
    fin_cases i <;> fin_cases j <;> simp [antipodalVariable] at hv ⊢ <;> omega,by
    intro b
    have hb : b.val∈({t,h,t+h} : Finset ℕ) :=
      (congrArg (fun s : Finset ℕ => b.val∈s) ha).mp b.property
    simp only [Finset.mem_insert,Finset.mem_singleton] at hb
    rcases hb with hb|hb|hb
    · exact ⟨0,Subtype.ext hb.symm⟩
    · exact ⟨1,Subtype.ext hb.symm⟩
    · exact ⟨2,Subtype.ext hb.symm⟩⟩

theorem antipodal_sum (h t : ℕ) (ht0 : 0<t) (ht : t<h) (ha : D.a={t,h,t+h})
    (f : D.a → ℕ) : ∑ b : D.a,f b=
      f (D.antipodalVariable h t ha 0)+f (D.antipodalVariable h t ha 1)+f (D.antipodalVariable h t ha 2) := by
  rw [←(D.antipodalVariableEquiv h t ht0 ht ha).sum_comp f]
  change (∑ i : Fin 3,f (D.antipodalVariable h t ha i))=_
  simp [Fin.sum_univ_succ,add_assoc]

theorem antipodal_internalPoint (h t : ℕ) (ht0 : 0<t) (ht : t<h)
    (ha : D.a={t,h,t+h}) (β : D.a →₀ ℕ) :
    D.internalPoint β=D.antipodalPoint h t ha
      (β (D.antipodalVariable h t ha 0)) (β (D.antipodalVariable h t ha 1))
      (β (D.antipodalVariable h t ha 2)) := by
  apply Subtype.ext
  apply Prod.ext
  · change D.coreDegree (D.internalPoint β)=_
    rw [D.internalPoint_degree,D.antipodal_sum h t ht0 ht ha]
    exact (D.antipodalPoint_degree h t ha _ _ _).symm
  · change D.coreOffset (D.internalPoint β)=_
    rw [D.internalPoint_offset,D.antipodal_sum h t ht0 ht ha]
    simp only [antipodalVariable,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
    exact (D.antipodalPoint_offset h t ha _ _ _).symm

/-- The standard monomials of k[y,z,w]/(yz,z²,zw,(y,w)^h), with
variables identified with the original three internal offsets. -/
def AntipodalStandard (h t : ℕ) (ha : D.a={t,h,t+h}) (β : D.a →₀ ℕ) : Prop :=
  (β (D.antipodalVariable h t ha 1)=0 ∧
      β (D.antipodalVariable h t ha 0)+β (D.antipodalVariable h t ha 2)<h) ∨
  (β (D.antipodalVariable h t ha 0)=0 ∧ β (D.antipodalVariable h t ha 1)=1 ∧
      β (D.antipodalVariable h t ha 2)=0)

theorem antipodal_standard_iff_minimal (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h})
    (β : D.a →₀ ℕ) : D.AntipodalStandard h t ha β ↔ D.CoreMinimal (D.internalPoint β) := by
  rw [D.antipodal_internalPoint h t ht0 ht ha β]
  constructor
  · rintro (⟨hy,hn⟩|⟨hx,hy,hz⟩)
    · rw [hy]
      exact D.antipodal_pure_minimal h t hu hc ha _ _ hn
    · rw [hx,hy,hz]
      exact D.antipodal_middle_minimal h t ha
  · intro hm
    by_cases hy : 0<β (D.antipodalVariable h t ha 1)
    · right
      exact D.antipodal_middle_isolated h t hu ha _ _ _ hm hy
    · left
      have hy0 : β (D.antipodalVariable h t ha 1)=0 := by omega
      refine ⟨hy0,?_⟩
      rw [hy0] at hm
      exact D.antipodal_pure_degree_lt h t hu hh ht ha _ _ hm

/-- Even though the full exponent-to-core map need not be injective,
it is injective over every surviving point of the actual quotient. -/
theorem antipodal_minimal_exponent_injective (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h})
    (β γ : D.a →₀ ℕ) (hm : D.CoreMinimal (D.internalPoint β))
    (he : D.internalPoint β=D.internalPoint γ) : β=γ := by
  have hmγ : D.CoreMinimal (D.internalPoint γ) := he ▸ hm
  have hb := (D.antipodal_standard_iff_minimal h t hu hh ht0 ht hc ha β).mpr hm
  have hg := (D.antipodal_standard_iff_minimal h t hu hh ht0 ht hc ha γ).mpr hmγ
  have hd := congrArg D.coreDegree he
  have ho := congrArg D.coreOffset he
  rw [D.antipodal_internalPoint h t ht0 ht ha,D.antipodal_internalPoint h t ht0 ht ha] at hd ho
  rw [D.antipodalPoint_degree,D.antipodalPoint_degree] at hd
  rw [D.antipodalPoint_offset,D.antipodalPoint_offset] at ho
  have hn : 0<h := by omega
  rcases hb with ⟨hb1,hbn⟩|⟨hb0,hb1,hb2⟩ <;>
    rcases hg with ⟨hg1,hgn⟩|⟨hg0,hg1,hg2⟩
  · have hz : β (D.antipodalVariable h t ha 2)=γ (D.antipodalVariable h t ha 2) := by
      nlinarith only [hd,ho,hn,hb1,hg1]
    have hx : β (D.antipodalVariable h t ha 0)=γ (D.antipodalVariable h t ha 0) := by omega
    ext b
    obtain ⟨i,hi⟩ := (D.antipodalVariableEquiv h t ht0 ht ha).surjective b
    have hi' : D.antipodalVariable h t ha i=b := hi
    rw [←hi']
    fin_cases i
    · exact hx
    · exact hb1.trans hg1.symm
    · exact hz
  · have hsum : β (D.antipodalVariable h t ha 0)+β (D.antipodalVariable h t ha 2)=1 := by omega
    have hcases : β (D.antipodalVariable h t ha 2)=0 ∨ β (D.antipodalVariable h t ha 2)=1 := by omega
    rcases hcases with hz|hz <;> rw [hb1,hg0,hg1,hg2,hz] at ho <;> nlinarith only [ho,hsum,ht0,ht,hz]
  · have hsum : γ (D.antipodalVariable h t ha 0)+γ (D.antipodalVariable h t ha 2)=1 := by omega
    have hcases : γ (D.antipodalVariable h t ha 2)=0 ∨ γ (D.antipodalVariable h t ha 2)=1 := by omega
    rcases hcases with hz|hz <;> rw [hb0,hb1,hb2,hg1,hz] at ho <;> nlinarith only [ho,hsum,ht0,ht,hz]
  · ext b
    obtain ⟨i,hi⟩ := (D.antipodalVariableEquiv h t ht0 ht ha).surjective b
    have hi' : D.antipodalVariable h t ha i=b := hi
    rw [←hi']
    fin_cases i
    · exact hb0.trans hg0.symm
    · exact hb1.trans hg1.symm
    · exact hb2.trans hg2.symm


variable (k : Type) [Field k]

theorem antipodal_surviving_coeff (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h})
    (f : D.InternalRing k) (β : D.a →₀ ℕ) (hm : D.CoreMinimal (D.internalPoint β)) :
    (D.internalToCore k f).coeff (D.internalPoint β)=f.coeff β := by
  rw [D.internalToCore_mapDomain]
  change (AddMonoidAlgebra.mapDomain D.internalPoint f).coeff (D.internalPoint β)=f.coeff β
  rw [AddMonoidAlgebra.coeff_mapDomain]
  rw [Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.sum_eq_single β,Finsupp.single_eq_same]
  · intro γ _ hγ
    apply Finsupp.single_eq_of_ne'
    intro he
    exact hγ (D.antipodal_minimal_exponent_injective h t hu hh ht0 ht hc ha β γ hm he.symm).symm
  · intro _
    rw [Finsupp.single_zero,Finsupp.coe_zero,Pi.zero_apply]

/-- The actual kernel is coefficientwise monomial; this is derived
from surviving actual basis points rather than asserted from a Hilbert table. -/
theorem antipodal_kernel_coefficients (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h})
    (f : D.InternalRing k) : D.internalToQCore k f=0 ↔
      ∀ β∈f.support,¬D.AntipodalStandard h t ha β := by
  constructor
  · intro hf β hβ hs
    have hm := (D.antipodal_standard_iff_minimal h t hu hh ht0 ht hc ha β).mp hs
    change Ideal.Quotient.mk _ (D.internalToCore k f)=0 at hf
    have hz := (D.coreEndpointIdeal_coeff_zero k _).mp (Ideal.Quotient.eq_zero_iff_mem.mp hf)
      (D.internalPoint β) hm
    rw [D.antipodal_surviving_coeff k h t hu hh ht0 ht hc ha f β hm] at hz
    exact (Finsupp.mem_support_iff.mp hβ) hz
  · intro hs
    have himg : Ideal.span ((fun β : D.a →₀ ℕ => MvPolynomial.monomial β (1:k)) ''
        {β | ¬D.AntipodalStandard h t ha β}) ≤ RingHom.ker (D.internalToQCore k).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨β,hβ,rfl⟩
      exact (D.QCore_internal_monomial_zero k β).mpr
        (fun hm => hβ ((D.antipodal_standard_iff_minimal h t hu hh ht0 ht hc ha β).mpr hm))
    apply himg
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro β hβ
    exact ⟨β,hs β hβ,le_rfl⟩

/-- Standard monomials determine this monomial ideal in the original
internal polynomial ring. The explicit finite generators are identified below. -/
noncomputable def antipodalMonomialIdeal (h t : ℕ) (ha : D.a={t,h,t+h}) : Ideal (D.InternalRing k) :=
  Ideal.span ((fun β : D.a →₀ ℕ => MvPolynomial.monomial β (1:k)) ''
    {β | ¬D.AntipodalStandard h t ha β})

theorem antipodal_kernel_ideal (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) :
    RingHom.ker (D.internalToQCore k).toRingHom=D.antipodalMonomialIdeal k h t ha := by
  apply le_antisymm
  · intro f hf
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro β hβ
    exact ⟨β,(D.antipodal_kernel_coefficients k h t hu hh ht0 ht hc ha f).mp hf β hβ,le_rfl⟩
  · apply Ideal.span_le.mpr
    rintro _ ⟨β,hβ,rfl⟩
    exact (D.QCore_internal_monomial_zero k β).mpr
      (fun hm => hβ ((D.antipodal_standard_iff_minimal h t hu hh ht0 ht hc ha β).mpr hm))

/-- Algebra presentation of the same actual QC, with the original
internal variables and the kernel proved coefficient by coefficient. -/
noncomputable def antipodalMonomialPresentation (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) :
    (D.InternalRing k ⧸ D.antipodalMonomialIdeal k h t ha) ≃ₐ[k] D.QCore k :=
  (Ideal.quotientEquivAlgOfEq k (D.antipodal_kernel_ideal k h t hu hh ht0 ht hc ha).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (D.internalToQCore_surjective k))
end NSP14.Endpoint.Data
