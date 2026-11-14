module
public import NSP14.Width.FiveHoleCore
public import Mathlib.Algebra.MvPolynomial.Division
public import NSP14.Width.CoreIdealPresentation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

def FiveHoleStandard (v : Fin 3 ≃ D.a) (β : D.a →₀ ℕ) : Prop :=
  β (v 0)+β (v 1)+β (v 2) ≤ 2 ∧ (β (v 0)=0 ∨ (β (v 1)=0 ∧ β (v 2)=0)) ∧
    β (v 1) ≤ 1 ∧ β (v 2) ≤ 1

theorem fiveHole_generator_le (v : Fin 3 ≃ D.a) (β : D.a →₀ ℕ) (i : Fin 5)
    (hb : ∀ j : Fin 3,D.fiveHoleExponent v i (v j) ≤ β (v j)) : D.fiveHoleExponent v i ≤ β := by
  intro b
  obtain ⟨j,hj⟩ := v.surjective b
  rw [←hj]
  exact hb j

theorem fiveHole_two_survive (hu : D.u=5) (flip : Bool) (v : Fin 3 ≃ D.a)
    (hv : ∀ i,(v i).val=fiveHoleValues flip i) (which : Bool) :
    D.CoreMinimal (if which then D.triplePoint v 0 1 1 else D.triplePoint v 2 0 0) := by
  have ha := D.triple_internal_offsets v
  cases which <;> apply D.degree_two_minimal_of_missing
  all_goals cases flip <;> norm_num [triplePoint_degree,triplePoint_offset,offsets,ha,hu,hv,fiveHoleValues]

theorem fiveHole_standard_of_no_generator (v : Fin 3 ≃ D.a) (β : D.a →₀ ℕ)
    (hnot : ∀ i : Fin 5,¬D.fiveHoleExponent v i ≤ β) : D.FiveHoleStandard v β := by
  have hx2 : β (v 0) ≤ 2 := by
    by_contra hn
    apply hnot 4
    apply D.fiveHole_generator_le v β 4
    intro j
    fin_cases j <;> simp [fiveHoleExponent,v.injective.eq_iff]
    omega
  have hy : β (v 1) ≤ 1 := by
    by_contra hn
    apply hnot 2
    apply D.fiveHole_generator_le v β 2
    intro j
    fin_cases j <;> simp [fiveHoleExponent,v.injective.eq_iff]
    omega
  have hz : β (v 2) ≤ 1 := by
    by_contra hn
    apply hnot 3
    apply D.fiveHole_generator_le v β 3
    intro j
    fin_cases j <;> simp [fiveHoleExponent,v.injective.eq_iff]
    omega
  have hxy : β (v 0)=0 ∨ β (v 1)=0 := by
    by_contra! hn
    apply hnot 0
    apply D.fiveHole_generator_le v β 0
    intro j
    fin_cases j <;> simp [fiveHoleExponent,v.injective.eq_iff] <;> omega
  have hxz : β (v 0)=0 ∨ β (v 2)=0 := by
    by_contra! hn
    apply hnot 1
    apply D.fiveHole_generator_le v β 1
    intro j
    fin_cases j <;> simp [fiveHoleExponent,v.injective.eq_iff] <;> omega
  have hcross : β (v 0)=0 ∨ (β (v 1)=0 ∧ β (v 2)=0) := by tauto
  refine ⟨?_,hcross,hy,hz⟩
  rcases hcross with hx|⟨hy0,hz0⟩ <;> omega

variable (k : Type) [Field k]
include k in
theorem fiveHole_minimal_standard (hq : D.q=3) (hu : D.u=5) (flip : Bool)
    (v : Fin 3 ≃ D.a) (hv : ∀ i,(v i).val=fiveHoleValues flip i)
    (β : D.a →₀ ℕ) (hm : D.CoreMinimal (D.internalPoint β)) : D.FiveHoleStandard v β := by
  have hnot (i : Fin 5) : ¬D.fiveHoleExponent v i ≤ β := by
    intro hle
    have hdvd : MvPolynomial.monomial (D.fiveHoleExponent v i) (1:k) ∣ MvPolynomial.monomial β (1:k) :=
      (MvPolynomial.monomial_dvd_monomial (r:=(1:k)) (s:=(1:k))).mpr ⟨Or.inr hle,dvd_rfl⟩
    obtain ⟨f,hf⟩ := hdvd
    have hz : D.internalToQCore k (MvPolynomial.monomial β (1:k))=0 := by
      rw [hf,map_mul]
      have hgen := D.fiveHole_generators_zero k hq hu flip v hv i
      change D.internalToQCore k (MvPolynomial.monomial (D.fiveHoleExponent v i) 1)=0 at hgen
      rw [hgen,zero_mul]
    exact ((D.QCore_internal_monomial_zero k β).mp hz) hm
  have hd := D.fiveHole_minimal_degree hq hu ⟨_,hm⟩
  change D.coreDegree (D.internalPoint β) ≤ 2 at hd
  rw [D.triple_internalPoint v,D.triplePoint_degree] at hd
  exact D.fiveHole_standard_of_no_generator v β hnot

theorem fiveHole_standard_minimal (hu : D.u=5) (flip : Bool) (v : Fin 3 ≃ D.a)
    (hv : ∀ i,(v i).val=fiveHoleValues flip i) (β : D.a →₀ ℕ)
    (hs : D.FiveHoleStandard v β) : D.CoreMinimal (D.internalPoint β) := by
  rcases hs with ⟨hd,hcross,hy,hz⟩
  rw [D.triple_internalPoint v]
  have hx2 : β (v 0) ≤ 2 := by omega
  interval_cases hx : β (v 0) <;> interval_cases hy' : β (v 1) <;> interval_cases hz' : β (v 2)
  all_goals first
    | omega
    | simpa only [triplePoint,zero_nsmul,zero_add,add_zero] using D.coreZero_minimal
    | simpa only [triplePoint,zero_nsmul,one_nsmul,zero_add,add_zero] using D.internal_generator_minimal (v 0)
    | simpa only [triplePoint,zero_nsmul,one_nsmul,zero_add,add_zero] using D.internal_generator_minimal (v 1)
    | simpa only [triplePoint,zero_nsmul,one_nsmul,zero_add,add_zero] using D.internal_generator_minimal (v 2)
    | exact D.fiveHole_two_survive hu flip v hv false
    | exact D.fiveHole_two_survive hu flip v hv true


include k in
theorem fiveHole_minimal_exponent_injective (hq : D.q=3) (hu : D.u=5) (flip : Bool)
    (v : Fin 3 ≃ D.a) (hv : ∀ i,(v i).val=fiveHoleValues flip i)
    (β γ : D.a →₀ ℕ) (hm : D.CoreMinimal (D.internalPoint β))
    (he : D.internalPoint β=D.internalPoint γ) : β=γ := by
  have hβ := D.fiveHole_minimal_standard k hq hu flip v hv β hm
  have hγ := D.fiveHole_minimal_standard k hq hu flip v hv γ (he ▸ hm)
  have hd := congrArg D.coreDegree he
  have ho := congrArg D.coreOffset he
  rw [D.triple_internalPoint v,D.triple_internalPoint v,D.triplePoint_degree,D.triplePoint_degree] at hd
  rw [D.triple_internalPoint v,D.triple_internalPoint v,D.triplePoint_offset,D.triplePoint_offset] at ho
  simp_rw [hv] at ho
  rcases hβ with ⟨hβd,hβc,hβy,hβz⟩
  rcases hγ with ⟨hγd,hγc,hγy,hγz⟩
  have hcoords : β (v 0)=γ (v 0) ∧ β (v 1)=γ (v 1) ∧ β (v 2)=γ (v 2) := by
    cases flip <;> norm_num [fiveHoleValues] at ho <;> omega
  ext b
  obtain ⟨i,hi⟩ := v.surjective b
  rw [←hi]
  fin_cases i
  · exact hcoords.1
  · exact hcoords.2.1
  · exact hcoords.2.2

theorem fiveHole_surviving_coeff (hq : D.q=3) (hu : D.u=5) (flip : Bool)
    (v : Fin 3 ≃ D.a) (hv : ∀ i,(v i).val=fiveHoleValues flip i)
    (f : D.InternalRing k) (β : D.a →₀ ℕ) (hm : D.CoreMinimal (D.internalPoint β)) :
    (D.internalToCore k f).coeff (D.internalPoint β)=f.coeff β := by
  rw [D.internalToCore_mapDomain]
  change (AddMonoidAlgebra.mapDomain D.internalPoint f).coeff (D.internalPoint β)=f.coeff β
  rw [AddMonoidAlgebra.coeff_mapDomain,Finsupp.mapDomain,Finsupp.sum_apply,Finsupp.sum_eq_single β,Finsupp.single_eq_same]
  · intro γ _ hγ
    apply Finsupp.single_eq_of_ne'
    intro he
    exact hγ (D.fiveHole_minimal_exponent_injective k hq hu flip v hv β γ hm he.symm).symm
  · intro _
    rw [Finsupp.single_zero,Finsupp.coe_zero,Pi.zero_apply]

/-- The actual kernel has the five explicitly verified generators. -/
theorem fiveHole_kernel (hq : D.q=3) (hu : D.u=5) (flip : Bool)
    (v : Fin 3 ≃ D.a) (hv : ∀ i,(v i).val=fiveHoleValues flip i) :
    RingHom.ker (D.internalToQCore k).toRingHom=Ideal.span (Set.range (D.fiveHoleGenerator k v)) := by
  apply le_antisymm
  · intro f hf
    have hspan : Set.range (D.fiveHoleGenerator k v)=
        (fun β => MvPolynomial.monomial β (1:k)) '' Set.range (D.fiveHoleExponent v) :=
      by
        change Set.range ((fun β : D.a →₀ ℕ => MvPolynomial.monomial β (1:k)) ∘ D.fiveHoleExponent v)=_
        exact Set.range_comp _ _
    rw [hspan]
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro β hβ
    by_contra! hnog
    have hs : D.FiveHoleStandard v β := D.fiveHole_standard_of_no_generator v β (by
      intro i
      exact hnog (D.fiveHoleExponent v i) ⟨i,rfl⟩)
    have hm := D.fiveHole_standard_minimal hu flip v hv β hs
    change Ideal.Quotient.mk _ (D.internalToCore k f)=0 at hf
    have hz := (D.coreEndpointIdeal_coeff_zero k _).mp (Ideal.Quotient.eq_zero_iff_mem.mp hf)
      (D.internalPoint β) hm
    rw [D.fiveHole_surviving_coeff k hq hu flip v hv f β hm] at hz
    exact (Finsupp.mem_support_iff.mp hβ) hz
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact D.fiveHole_generators_zero k hq hu flip v hv i

attribute [local instance] MvPolynomial.gradedAlgebra
theorem fiveHole_first (hq : D.q=3) (hu : D.u=5) (flip : Bool)
    (v : Fin 3 ≃ D.a) (hv : ∀ i,(v i).val=fiveHoleValues flip i) :
    NSP14.Homological.totalBetti k D.a (D.QCoreModule k) 1 ≤ 5 := by
  have hker := D.fiveHole_kernel k hq hu flip v hv
  have hhom : (RingHom.ker (D.internalToQCore k).toRingHom).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule D.a k) := by
    rw [hker]
    apply Ideal.homogeneous_span
    rintro _ ⟨i,rfl⟩
    exact ⟨(D.fiveHoleExponent v i).degree,MvPolynomial.isHomogeneous_monomial (1:k) rfl⟩
  exact D.QCore_first_le_kernel_generators k (D.fiveHoleGenerator k v) hker hhom
end NSP14.Endpoint.Data
