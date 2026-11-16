module
public import NSP14.Width.AntipodalCore
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

/-- Every original core point counts the t-residue letters by a number
at most its actual degree. Endpoint and middle letters have zero residue modulo h. -/
theorem antipodal_mod_representation (h t : ℕ) (hu : D.u=2*h)
    (ha : D.a={t,h,t+h}) (p : D.corePoints) :
    ∃ l j : ℕ,l ≤ D.coreDegree p ∧ D.coreOffset p=l*t+j*h := by
  change ∃ l j : ℕ,l ≤ p.val.1 ∧ p.val.2=l*t+j*h
  apply AddSubmonoid.closure_induction
    (motive:=fun p _ => ∃ l j : ℕ,l ≤ p.1 ∧ p.2=l*t+j*h) ?_ ?_ ?_ p.property
  · rintro p ⟨b,rfl⟩
    rcases (D.mem_offsets b.val).mp b.property with hb|hb|hb
    · exact ⟨0,0,by exact Nat.zero_le _,by simp [hb]⟩
    · exact ⟨0,2,by exact Nat.zero_le _,by simp [hb,hu]⟩
    · rw [ha] at hb
      simp only [Finset.mem_insert,Finset.mem_singleton] at hb
      rcases hb with hb|hb|hb
      · exact ⟨1,0,by change 1 ≤ 1; omega,by simp [hb]⟩
      · exact ⟨0,1,by exact Nat.zero_le _,by simp [hb]⟩
      · exact ⟨1,1,by change 1 ≤ 1; omega,by simp [hb]⟩
  · exact ⟨0,0,by simp,by simp⟩
  · rintro p q _ _ ⟨l,j,hl,hp⟩ ⟨l',j',hl',hq⟩
    exact ⟨l+l',j+j',by dsimp; omega,by dsimp; rw [hp,hq]; ring⟩

/-- Below h, the collective coprimality prevents an endpoint factor
in every genuine pure y/w word. No invertibility modulo 2h is assumed. -/
theorem antipodal_pure_minimal (h t : ℕ) (hu : D.u=2*h)
    (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) (x z : ℕ) (hn : x+z<h) :
    D.CoreMinimal (D.antipodalPoint h t ha x 0 z) := by
  by_contra hm
  rcases (D.core_not_minimal_iff_factor _).mp hm with ⟨q,hq⟩|⟨q,hq⟩
  all_goals
    obtain ⟨l,j,hl,hB⟩ := D.antipodal_mod_representation h t hu ha q
    have hd := congrArg D.coreDegree hq
    have ho := congrArg D.coreOffset hq
    simp only [D.antipodalPoint_degree,map_add] at hd
    simp only [D.antipodalPoint_offset,map_add] at ho
    have hl_lt : l<x+z := by
      change x+0+z=D.coreDegree q+1 at hd
      omega
    have hmod : (x+z)*t ≡ l*t [MOD h] := by
      have he : (x+z)*t+z*h=l*t+j*h ∨ (x+z)*t+z*h=l*t+(j+2)*h := by
        first
        | left
          change x*t+0*h+z*(t+h)=D.coreOffset q+0 at ho
          rw [hB] at ho
          nlinarith only [ho]
        | right
          change x*t+0*h+z*(t+h)=D.coreOffset q+D.u at ho
          rw [hB,hu] at ho
          nlinarith only [ho]
      rcases he with he|he
      all_goals
        have he' := congrArg (fun n : ℕ => n%h) he
        change (x+z)*t%h=l*t%h
        simpa only [Nat.add_mul_mod_self_right] using he'
    have he := hmod.cancel_right_of_coprime hc.symm.gcd_eq_one
    change ((x+z)%h)=(l%h) at he
    rw [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt (by omega)] at he
    omega

/-- The middle degree-one letter survives in the same actual quotient. -/
theorem antipodal_middle_minimal (h t : ℕ) (ha : D.a={t,h,t+h}) :
    D.CoreMinimal (D.antipodalPoint h t ha 0 1 0) := by
  simpa only [antipodalPoint,zero_nsmul,one_nsmul,zero_add,add_zero] using
    D.internal_generator_minimal (⟨h,by rw [ha]; simp⟩ : D.a)

theorem antipodalCandidate_minimal (h t : ℕ) (hu : D.u=2*h)
    (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h})
    (i : Option (Σ n : Fin h,Fin (n.val+1))) :
    D.CoreMinimal (D.antipodalCandidate h t ha i) := by
  rcases i with _|⟨n,z⟩
  · exact D.antipodal_middle_minimal h t ha
  · apply D.antipodal_pure_minimal h t hu hc ha
    have hz : z.val ≤ n.val := by have := z.isLt; omega
    have hn := n.isLt
    omega

/-- Distinct candidates give distinct genuine degree/offset points. -/
theorem antipodalCandidate_injective (h t : ℕ) (hh : 0<h) (ht0 : 0<t) (ht : t<h)
    (ha : D.a={t,h,t+h}) : Function.Injective (D.antipodalCandidate h t ha) := by
  intro i j he
  have hd := congrArg D.coreDegree he
  have ho := congrArg D.coreOffset he
  rcases i with _|⟨n,z⟩ <;> rcases j with _|⟨m,w⟩
  · rfl
  · simp only [antipodalCandidate,D.antipodalPoint_degree] at hd
    simp only [antipodalCandidate,D.antipodalPoint_offset] at ho
    have hw := w.isLt
    have hm : m.val=1 := by omega
    have hw01 : w.val=0 ∨ w.val=1 := by omega
    rcases hw01 with hwv|hwv <;> simp only [hm,hwv] at ho <;> norm_num at ho <;> omega
  · simp only [antipodalCandidate,D.antipodalPoint_degree] at hd
    simp only [antipodalCandidate,D.antipodalPoint_offset] at ho
    have hz := z.isLt
    have hn : n.val=1 := by omega
    have hz01 : z.val=0 ∨ z.val=1 := by omega
    rcases hz01 with hzv|hzv <;> simp only [hn,hzv] at ho <;> norm_num at ho <;> omega
  · have hz := z.isLt
    have hw := w.isLt
    simp only [antipodalCandidate,D.antipodalPoint_degree] at hd
    have hnm : n=m := Fin.ext (by omega)
    subst m
    simp only [antipodalCandidate,D.antipodalPoint_offset] at ho
    have hzw : z=w := by
      apply Fin.ext
      have hzle : z.val ≤ n.val := by omega
      have hwle : w.val ≤ n.val := by omega
      have hzs := Nat.sub_add_cancel hzle
      have hws := Nat.sub_add_cancel hwle
      nlinarith only [ho,hzs,hws,hh]
    subst w
    rfl


/-- The canonical finite normal forms are in bijection with the actual
QC basis. All point degrees and internal variables remain those of D. -/
noncomputable def antipodalBasisEquiv (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) :
    Option (Σ n : Fin h,Fin (n.val+1)) ≃ D.CoreMinimalIndex :=
  Equiv.ofBijective (D.antipodalBasisMap h t ha) ⟨by
    intro i j he
    have hi := D.antipodalCandidate_minimal h t hu hc ha i
    have hj := D.antipodalCandidate_minimal h t hu hc ha j
    have he' := congrArg Subtype.val he
    simp only [antipodalBasisMap,dite_eq_left hi,dite_eq_left hj] at he'
    exact D.antipodalCandidate_injective h t (by omega) ht0 ht ha he',
    D.antipodalBasisMap_surjective h t hu hh ht ha⟩

theorem antipodalBasisEquiv_value (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h})
    (i : Option (Σ n : Fin h,Fin (n.val+1))) :
    (D.antipodalBasisEquiv h t hu hh ht0 ht hc ha i).val=D.antipodalCandidate h t ha i := by
  change (D.antipodalBasisMap h t ha i).val=_
  rw [antipodalBasisMap,dite_eq_left (D.antipodalCandidate_minimal h t hu hc ha i)]

/-- The exact dimension is derived from the actual graded quotient basis. -/
theorem antipodal_coreP (k : Type) [Field k] (h t : ℕ) (hu : D.u=2*h)
    (hh : 4 ≤ h) (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) :
    D.coreP k=(h+1).choose 2+1 := by
  rw [coreP,Module.finrank_eq_card_basis (D.QCoreBasis k),
    ←Fintype.card_congr (D.antipodalBasisEquiv h t hu hh ht0 ht hc ha),antipodalCandidate_card]


/-- A canonical degree label on the actual finite normal forms. -/
def antipodalDegree (h : ℕ) : Option (Σ n : Fin h,Fin (n.val+1)) → ℕ
  | none => 1
  | some ⟨n,_⟩ => n.val

theorem antipodalBasisEquiv_degree (h t : ℕ) (hu : D.u=2*h) (hh : 4 ≤ h)
    (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h})
    (i : Option (Σ n : Fin h,Fin (n.val+1))) :
    D.coreDegree (D.antipodalBasisEquiv h t hu hh ht0 ht hc ha i).val=antipodalDegree h i := by
  rw [D.antipodalBasisEquiv_value]
  rcases i with _|⟨n,z⟩
  · simp [antipodalCandidate,antipodalDegree]
  · simp only [antipodalCandidate,antipodalDegree,D.antipodalPoint_degree]
    have hz := z.isLt
    omega

noncomputable def antipodalQCoreBasis (k : Type) [Field k] (h t : ℕ) (hu : D.u=2*h)
    (hh : 4 ≤ h) (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h}) :
    Module.Basis (Option (Σ n : Fin h,Fin (n.val+1))) k (D.QCore k) :=
  (D.QCoreBasis k).reindex (D.antipodalBasisEquiv h t hu hh ht0 ht hc ha).symm

theorem antipodalQCoreBasis_apply (k : Type) [Field k] (h t : ℕ) (hu : D.u=2*h)
    (hh : 4 ≤ h) (ht0 : 0<t) (ht : t<h) (hc : Nat.Coprime t h) (ha : D.a={t,h,t+h})
    (i : Option (Σ n : Fin h,Fin (n.val+1))) :
    D.antipodalQCoreBasis k h t hu hh ht0 ht hc ha i=
      Ideal.Quotient.mk _ (D.coreMonomial k (D.antipodalCandidate h t ha i)) := by
  rw [antipodalQCoreBasis,Module.Basis.reindex_apply,Equiv.symm_symm,D.QCoreBasis_apply,D.antipodalBasisEquiv_value]
end NSP14.Endpoint.Data
