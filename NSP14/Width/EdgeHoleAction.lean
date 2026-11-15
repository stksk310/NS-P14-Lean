module
public import NSP14.Width.EdgeHoleGeometry
public import NSP14.Width.FiveHoleTopRank
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data

/-- Only the actual missing integer and its actual alphabet equality. -/
structure OneHole (D : NSP14.Endpoint.Data) where
  h : ℕ
  pos : 0<h
  lt : h<D.u
  alphabet : D.a=Finset.Ioo 0 D.u \ {h}

noncomputable def oneHole (D : NSP14.Endpoint.Data) (hu : D.u=D.q+2) : D.OneHole :=
  let hw := D.one_missing_offset hu
  ⟨hw.choose,hw.choose_spec.1,hw.choose_spec.2.1,hw.choose_spec.2.2⟩

namespace OneHole
variable {D : NSP14.Endpoint.Data} (H : D.OneHole)

theorem variable_ne (b : D.a) : b.val≠H.h := by
  have hm := (congrArg (fun s : Finset ℕ => b.val∈s) H.alphabet).mp b.property
  exact (by simpa only [Finset.mem_singleton] using (Finset.mem_sdiff.mp hm).2)

noncomputable def mate (b : D.a) : D.a :=
  ⟨if b.val<H.h then H.h-b.val else H.h+D.u-b.val,by
    apply (congrArg (fun s : Finset ℕ => (if b.val<H.h then H.h-b.val else H.h+D.u-b.val)∈s) H.alphabet).mpr
    apply Finset.mem_sdiff.mpr
    have hp := D.a_pos b.val b.property
    have hu := D.a_lt b.val b.property
    have hn := H.variable_ne b
    have hh := H.lt
    split_ifs with hb <;> simp only [Finset.mem_Ioo,Finset.mem_singleton] <;> omega⟩

def side (b : D.a) : Bool := decide (H.h<b.val)

theorem mate_sum (b : D.a) : b.val+(H.mate b).val=if H.side b then H.h+D.u else H.h := by
  have hp := D.a_pos b.val b.property
  have hu := D.a_lt b.val b.property
  have hn := H.variable_ne b
  by_cases hb : b.val<H.h
  · have hn' : ¬H.h<b.val := by omega
    simp only [mate,hb,ite_true,side,hn',decide_false,Bool.false_eq_true,ite_false]
    omega
  · have hn' : H.h<b.val := by omega
    simp only [mate,hb,ite_false,side,hn',decide_true,ite_true]
    omega

theorem mate_side (b : D.a) : H.side (H.mate b)=H.side b := by
  have hp := D.a_pos b.val b.property
  have hu := D.a_lt b.val b.property
  have hn := H.variable_ne b
  by_cases hb : b.val<H.h
  · have hn' : ¬H.h<b.val := by omega
    have hm : ¬H.h<H.h-b.val := by omega
    simp [side,mate,hb,hn',hm]
  · have hn' : H.h<b.val := by omega
    have hm : H.h<H.h+D.u-b.val := by omega
    simp [side,mate,hb,hn',hm]

theorem mate_involutive : Function.Involutive H.mate := by
  intro b
  apply Subtype.ext
  have h1 := H.mate_sum b
  have h2 := H.mate_sum (H.mate b)
  rw [H.mate_side b] at h2
  omega

noncomputable def pair (b : D.a) : D.corePoints :=
  D.coreGeneratorPoint (D.internalVariable b)+D.coreGeneratorPoint (D.internalVariable (H.mate b))

theorem pair_degree (b : D.a) : D.coreDegree (H.pair b)=2 := rfl

theorem pair_offset (b : D.a) : D.coreOffset (H.pair b)=if H.side b then H.h+D.u else H.h := H.mate_sum b

theorem missing_not_offset : H.h∉D.offsets := by
  rw [D.mem_offsets,H.alphabet]
  simp only [Finset.mem_sdiff,Finset.mem_singleton,not_or]
  exact ⟨by have := H.pos; omega,by have := H.lt; omega,fun hm => hm.2 trivial⟩

theorem pair_minimal (b : D.a) : D.CoreMinimal (H.pair b) := by
  apply D.degree_two_minimal_of_missing _ (H.pair_degree b)
  · rw [H.pair_offset b]
    split_ifs
    · intro hm
      have := D.offset_le hm
      have := H.pos
      omega
    · exact H.missing_not_offset
  · rw [H.pair_offset b]
    split_ifs
    · right
      simpa only [Nat.add_sub_cancel_right] using H.missing_not_offset
    · exact Or.inl H.lt

noncomputable def quadraticIndex (b : D.a) : D.CoreMinimalIndex := ⟨H.pair b,H.pair_minimal b⟩

theorem pair_same_side (b c : D.a) (hs : H.side b=H.side c) : H.pair b=H.pair c := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact (H.pair_offset b).trans (by rw [hs]; exact (H.pair_offset c).symm)

theorem side_false_iff (b : D.a) : H.side b=false ↔ b.val<H.h := by
  have hn := H.variable_ne b
  simp only [side,decide_eq_false_iff_not]
  omega

theorem side_true_iff (b : D.a) : H.side b=true ↔ H.h<b.val := by simp [side]

/-- A fixed linear coefficient can hit only its unique partner, in its
own quadratic block. -/
theorem product_point_eq (b c v : D.a) :
    D.coreGeneratorPoint (D.internalVariable v)+
      D.coreGeneratorPoint (D.internalVariable (H.mate b))=H.pair c ↔
        H.side b=H.side c ∧ v=b := by
  have hp := D.a_pos v.val v.property
  have hu := D.a_lt v.val v.property
  have hm := H.mate_sum b
  have hml := D.a_lt (H.mate b).val (H.mate b).property
  have hmp := D.a_pos (H.mate b).val (H.mate b).property
  have ho := H.pair_offset c
  have hpiff : (D.coreGeneratorPoint (D.internalVariable v)+
      D.coreGeneratorPoint (D.internalVariable (H.mate b))=H.pair c) ↔
        v.val+(H.mate b).val=(if H.side c then H.h+D.u else H.h) := by
    constructor
    · intro he
      have hx := congrArg D.coreOffset he
      exact hx.trans ho
    · intro he
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact he.trans ho.symm
  rw [hpiff]
  have hv : v=b ↔ v.val=b.val := ⟨congrArg Subtype.val,Subtype.ext⟩
  rw [hv]
  by_cases hs : H.side b=H.side c
  · simp only [hs,true_and]
    rw [←hs]
    cases hb : H.side b <;> simp only [hb,Bool.false_eq_true,ite_false,ite_true] at hm ⊢ <;> omega
  · simp only [hs,false_and,iff_false]
    cases hb : H.side b
    · have hc : H.side c=true := by cases hc : H.side c <;> simp_all
      rw [hc]
      have hmb : (H.mate b).val<H.h := (H.side_false_iff _).mp (by rw [H.mate_side b,hb])
      simp only [ite_true]
      omega
    · have hc : H.side c=false := by cases hc : H.side c <;> simp_all
      rw [hc]
      have hmb : H.h<(H.mate b).val := (H.side_true_iff _).mp (by rw [H.mate_side b,hb])
      simp only [Bool.false_eq_true,ite_false]
      omega

variable (k : Type) [Field k]
theorem quadratic_variable_coefficient (b c v : D.a) :
    D.coreRow k (H.quadraticIndex c)
      ((MvPolynomial.X v : D.InternalRing k) •
        D.coreColumn k (D.coreGeneratorPoint (D.internalVariable (H.mate b))))=
      if H.side b=H.side c ∧ v=b then 1 else 0 := by
  rw [D.coreRow_variable_column]
  change (if _=H.pair c then (1:k) else 0)=_
  simp only [H.product_point_eq]

theorem linear_variable_linear_zero (b v w : D.a) :
    D.QCoreLinearFunctional k v ((MvPolynomial.X w : D.InternalRing k) •
      D.coreColumn k (D.coreGeneratorPoint (D.internalVariable (H.mate b))))=0 := by
  change D.coreRow k (D.internalMinimalIndex v) _=0
  rw [D.coreRow_variable_column]
  apply ite_eq_right
  intro he
  have hd := congrArg D.coreDegree he
  change (2:ℕ)=1 at hd
  omega

theorem quadratic_variable_unit_zero (b v : D.a) :
    D.coreRow k (H.quadraticIndex b) ((MvPolynomial.X v : D.InternalRing k) •D.QCoreUnit k)=0 := by
  have hz : D.QCoreUnit k=D.coreColumn k 0 := by
    change (D.QCoreCoefficientEquiv k).symm 1=(D.QCoreCoefficientEquiv k).symm _
    congr 1
  rw [hz,D.coreRow_variable_column]
  apply ite_eq_right
  intro he
  have hd := congrArg D.coreDegree he
  change (1:ℕ)=2 at hd
  omega
end OneHole
end NSP14.Endpoint.Data
