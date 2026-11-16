module
public import NSP14.Semigroup.Atoms
public import Mathlib.Algebra.Order.Ring.Int
@[expose] public section
open scoped Classical
namespace NSP14.ArithmeticSequence

/-- Genuine minimal arithmetic sequences, with d unrestricted apart from
positivity and gcd. In particular d is not specialized to interval targets. -/
structure Data where
  m : ℕ
  d : ℕ
  v : ℕ
  m_two : 2 ≤ m
  d_pos : 1 ≤ d
  v_pos : 1 ≤ v
  v_lt : v < m
  coprime : Nat.Coprime m d

namespace Data
variable (D : Data)
noncomputable def source : NumericalSemigroup where
  carrier :=
    { carrier := {x | ∃ l j : ℕ,j ≤ D.v*l ∧ x=l*D.m+j*D.d}
      zero_mem' := ⟨0,0,by simp,by simp⟩
      add_mem' := by
        rintro x y ⟨l,i,hi,hx⟩ ⟨n,j,hj,hy⟩
        refine ⟨l+n,i+j,by nlinarith,?_⟩
        rw [hx,hy]
        ring }
  conductor := D.m*(D.m+D.d)
  cofinite n hn := by
    have hc : Nat.gcd D.m (D.m+D.d)=1 := by simpa only [Nat.add_comm D.m D.d, Nat.gcd_add_self_right] using D.coprime.gcd_eq_one
    obtain ⟨a,b,he⟩ := Nat.exists_add_mul_eq_of_gcd_dvd_of_mul_pred_le D.m (D.m+D.d) n
      (by rw [hc];exact one_dvd _) (by
        exact (Nat.mul_le_mul (Nat.pred_le _) (Nat.pred_le _)).trans hn)
    refine ⟨a+b,b,?_,?_⟩
    · have hv := D.v_pos
      nlinarith
    · rw [← he]
      ring

@[simp] theorem mem_source (x : ℕ) : x∈D.source ↔ ∃ l j : ℕ,j≤D.v*l ∧ x=l*D.m+j*D.d := Iff.rfl

theorem generator_mem (i : ℕ) (hi : i≤D.v) : D.m+i*D.d ∈ D.source :=
  ⟨1,i,by simpa using hi,by simp⟩

theorem representation_length_pos {x l j : ℕ} (hx : 0<x) (hj : j≤D.v*l)
    (he : x=l*D.m+j*D.d) : 1≤l := by
  by_contra hn
  have hl : l=0 := by omega
  have hj0 : j=0 := by simp only [hl,Nat.mul_zero] at hj;omega
  simp only [hl,hj0,Nat.zero_mul,Nat.add_zero] at he
  omega

theorem multiplicity : D.source.multiplicity=D.m := by
  apply D.source.multiplicity_eq (by have := D.m_two;omega) (by simpa using D.generator_mem 0 (by omega))
  intro x hx hp
  obtain ⟨l,j,hj,he⟩ := hx
  have hl := D.representation_length_pos hp hj he
  have hm := Nat.mul_le_mul_right D.m hl
  nlinarith

theorem generator_atom (i : ℕ) (hi : i≤D.v) : D.source.IsAtom (D.m+i*D.d) := by
  refine ⟨D.generator_mem i hi,by have := D.m_two;omega,?_⟩
  intro x hx y hy he
  by_cases hx0 : x=0
  · exact Or.inl hx0
  by_cases hy0 : y=0
  · exact Or.inr hy0
  exfalso
  obtain ⟨a,b,hb,hx⟩ := hx
  obtain ⟨c,e,he',hy⟩ := hy
  have ha := D.representation_length_pos (by omega : 0<x) hb hx
  have hc := D.representation_length_pos (by omega : 0<y) he' hy
  have heq : D.m+i*D.d=(a+c)*D.m+(b+e)*D.d := by rw [he,hx,hy];ring
  have hbnd : b + e ≤ i := by
    have hm := Nat.mul_le_mul_right D.m (show 1≤a+c by omega)
    have hd := D.d_pos
    nlinarith
  have hmod : i*D.d ≡ (b+e)*D.d [MOD D.m] := by
    have h := congrArg (fun n => n%D.m) heq
    change (i*D.d)%D.m=((b+e)*D.d)%D.m
    simpa only [Nat.add_mod,Nat.mod_self,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod] using h
  have hcancel := hmod.cancel_right_of_coprime D.coprime.gcd_eq_one
  have hi' : i<D.m := hi.trans_lt D.v_lt
  have hb' : b+e<D.m := hbnd.trans_lt hi'
  have hie : i=b+e := by
    change i%D.m=(b+e)%D.m at hcancel
    simpa only [Nat.mod_eq_of_lt hi',Nat.mod_eq_of_lt hb'] using hcancel
  have hm := Nat.mul_le_mul_right D.m (show 2≤a+c by omega)
  have hp := D.m_two
  rw [hie] at heq
  omega

theorem atom_eq_generator {x : ℕ} (hx : D.source.IsAtom x) :
    ∃ i≤D.v,x=D.m+i*D.d := by
  obtain ⟨l,j,hj,he⟩ := hx.1
  have hl := D.representation_length_pos hx.2.1 hj he
  by_cases hl1 : l=1
  · refine ⟨j,by simpa only [hl1,Nat.mul_one] using hj,?_⟩
    simpa only [hl1,Nat.one_mul] using he
  have hl2 : 2≤l := by omega
  let a := min D.v j
  let b := j-a
  have ha : a≤D.v := Nat.min_le_left _ _
  have haj : a≤j := Nat.min_le_right _ _
  have hb : b≤D.v*(l-1) := by
    dsimp [a,b]
    have he := Nat.sub_add_cancel (show 1≤l by omega)
    by_cases hv : D.v≤j
    · rw [min_eq_left hv]
      have hmul : D.v * (l-1) + D.v = D.v * l := by nlinarith [congrArg (D.v * ·) he]
      omega
    · rw [min_eq_right (by omega : j≤D.v)]
      simp
  have hu := D.generator_mem a ha
  have hw : (l-1)*D.m+b*D.d ∈ D.source := ⟨l-1,b,hb,rfl⟩
  have hsplit : x=(D.m+a*D.d)+((l-1)*D.m+b*D.d) := by
    have hl' := Nat.sub_add_cancel (show 1≤l by omega)
    have hj' : b+a=j := Nat.sub_add_cancel haj
    nlinarith [he]
  obtain hz|hz := hx.2.2 _ hu _ hw hsplit
  · have := D.m_two
    omega
  · have hm : 0<(l-1)*D.m := Nat.mul_pos (by omega) (by have := D.m_two;omega)
    omega

theorem atoms : D.source.atoms=Finset.image (fun i : Fin (D.v+1) => D.m+i.val*D.d) Finset.univ := by
  ext x
  rw [D.source.mem_atoms_iff]
  constructor
  · intro hx
    obtain ⟨i,hi,rfl⟩ := D.atom_eq_generator hx
    exact Finset.mem_image.mpr ⟨⟨i,by omega⟩,Finset.mem_univ _,rfl⟩
  · intro hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact D.generator_atom i.val (by have := i.isLt;omega)

theorem embeddingDimension : D.source.embeddingDimension=D.v+1 := by
  unfold NumericalSemigroup.embeddingDimension
  rw [D.atoms,Finset.card_image_of_injective]
  · simp
  · intro a b he
    apply Fin.ext
    have hd := D.d_pos
    nlinarith
end Data
end NSP14.ArithmeticSequence
