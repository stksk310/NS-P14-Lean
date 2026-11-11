module
public import NSP14.Semigroup.IntervalCompletion
public import Mathlib.NumberTheory.FrobeniusNumber
public import Mathlib.Algebra.GCDMonoid.Finset
@[expose] public section
open scoped Classical
namespace NSP14.Endpoint

/-- The broad endpoint hypotheses. In particular no bound d*u<m,
no gcd(m,u)=1 and no Cohen--Macaulay hypothesis is present. -/
structure Data where
  m : ℕ
  d : ℕ
  u : ℕ
  a : Finset ℕ
  q_two : 2 ≤ a.card
  a_pos : ∀ b∈a,0 < b
  a_lt : ∀ b∈a,b < u
  u_lt : u < m
  d_pos : 1 ≤ d
  offsets_coprime : Nat.gcd (a.gcd id) u=1
  coprime : Nat.Coprime m d

namespace Data
variable (D : Data)
def q : ℕ := D.a.card

def offsets : Finset ℕ := insert 0 (insert D.u D.a)
def generators : Finset ℕ := D.offsets.image (fun b => D.m+b*D.d)

@[simp] theorem mem_offsets (b : ℕ) : b∈D.offsets ↔ b=0 ∨ b=D.u ∨ b∈D.a := by
  simp only [offsets,Finset.mem_insert]

theorem u_pos : 0 < D.u := by
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < D.a.card by have := D.q_two;omega)
  have := D.a_pos b hb
  have := D.a_lt b hb
  omega

theorem m_pos : 0 < D.m := D.u_pos.trans D.u_lt

theorem offset_le {b : ℕ} (hb : b∈D.offsets) : b≤D.u := by
  rcases (D.mem_offsets b).mp hb with rfl|rfl|hb
  · omega
  · rfl
  · exact (D.a_lt b hb).le

theorem offsets_card : D.offsets.card=D.q+2 := by
  have h0 : 0∉D.a := fun h => Nat.lt_irrefl 0 (D.a_pos 0 h)
  have hu : D.u∉D.a := fun h => Nat.lt_irrefl D.u (D.a_lt D.u h)
  rw [offsets,Finset.card_insert_of_notMem (by simpa only [Finset.mem_insert,not_or] using And.intro (Nat.ne_of_lt D.u_pos) h0),Finset.card_insert_of_notMem hu]
  rfl

theorem generator_injective : Function.Injective (fun b : ℕ => D.m+b*D.d) := by
  intro a b h
  have := D.d_pos
  nlinarith

theorem generator_mem (b : ℕ) (hb : b∈D.offsets) : D.m+b*D.d∈D.generators :=
  Finset.mem_image.mpr ⟨b,hb,rfl⟩

theorem generators_setGcd : Nat.setGcd (D.generators : Set ℕ)=1 := by
  let g := Nat.setGcd (D.generators : Set ℕ)
  have hm : g∣D.m := by
    simpa only [Nat.zero_mul,Nat.add_zero] using
      (Nat.setGcd_dvd_of_mem (D.generator_mem 0 (by simp)))
  have hc : Nat.Coprime g D.d := Nat.Coprime.of_dvd_left hm D.coprime
  have hoff (b : ℕ) (hb : b∈D.offsets) : g∣b := by
    have h := Nat.setGcd_dvd_of_mem (D.generator_mem b hb)
    have hd : g∣b*D.d := (Nat.dvd_add_iff_right hm).mpr h
    exact hc.dvd_of_dvd_mul_right hd
  apply Nat.dvd_one.mp
  rw [← D.offsets_coprime]
  exact Nat.dvd_gcd (Finset.dvd_gcd (fun b hb => hoff b (by simp [hb]))) (hoff D.u (by simp))

theorem cofinite_closure : ∃ c,∀ n,c≤n → n∈AddSubmonoid.closure (D.generators : Set ℕ) := by
  obtain ⟨c,hc⟩ := Nat.exists_mem_closure_of_ge (D.generators : Set ℕ)
  exact ⟨c,fun n hn => hc n hn (by rw [D.generators_setGcd];exact one_dvd _)⟩

noncomputable def source : NumericalSemigroup where
  carrier := AddSubmonoid.closure (D.generators : Set ℕ)
  conductor := Nat.find D.cofinite_closure
  cofinite := Nat.find_spec D.cofinite_closure

theorem source_generator (b : ℕ) (hb : b∈D.offsets) : D.m+b*D.d∈D.source :=
  AddSubmonoid.subset_closure (D.generator_mem b hb)

/-- Every actual representation has its real length and nonnegative
offset sum, before any endpoint-coordinate reduction. -/
theorem representation {x : ℕ} (hx : x∈D.source) :
    ∃ n B : ℕ,B≤D.u*n ∧ x=n*D.m+B*D.d := by
  apply AddSubmonoid.closure_induction (motive:=fun x _ => ∃ n B : ℕ,B≤D.u*n ∧ x=n*D.m+B*D.d) ?_ ?_ ?_ hx
  · intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨1,b,by simpa only [Nat.mul_one] using D.offset_le hb,by simp⟩
  · exact ⟨0,0,by simp,by simp⟩
  · rintro x y _ _ ⟨n,B,hB,rfl⟩ ⟨l,C,hC,rfl⟩
    exact ⟨n+l,B+C,by nlinarith,by ring⟩

theorem representation_length_pos {x n B : ℕ} (hx : 0 < x) (hB : B≤D.u*n)
    (he : x=n*D.m+B*D.d) : 1≤n := by
  by_contra hn
  have hn0 : n=0 := by omega
  have hB0 : B=0 := by simp only [hn0,Nat.mul_zero] at hB;omega
  simp only [hn0,hB0,Nat.zero_mul,Nat.zero_add] at he
  omega

theorem multiplicity : D.source.multiplicity=D.m := by
  apply D.source.multiplicity_eq D.m_pos (by simpa using D.source_generator 0 (by simp))
  intro x hx hp
  obtain ⟨n,B,hB,he⟩ := D.representation hx
  have hn := D.representation_length_pos hp hB he
  have hm := Nat.mul_le_mul_right D.m hn
  nlinarith

theorem generator_atom (b : ℕ) (hb : b∈D.offsets) : D.source.IsAtom (D.m+b*D.d) := by
  refine ⟨D.source_generator b hb,by have := D.m_pos;omega,?_⟩
  intro x hx y hy he
  by_cases hx0 : x=0
  · exact Or.inl hx0
  by_cases hy0 : y=0
  · exact Or.inr hy0
  exfalso
  obtain ⟨n,B,hB,hx⟩ := D.representation hx
  obtain ⟨l,C,hC,hy⟩ := D.representation hy
  have hn := D.representation_length_pos (by omega : 0 < x) hB hx
  have hl := D.representation_length_pos (by omega : 0 < y) hC hy
  have heq : D.m+b*D.d=(n+l)*D.m+(B+C)*D.d := by rw [he,hx,hy];ring
  have hbc : B+C≤b := by
    have h := Nat.mul_le_mul_right D.m (show 1≤n+l by omega)
    have := D.d_pos
    nlinarith
  have hmod : b*D.d ≡ (B+C)*D.d [MOD D.m] := by
    have h := congrArg (fun a => a%D.m) heq
    change (b*D.d)%D.m=((B+C)*D.d)%D.m
    simpa only [Nat.add_mod,Nat.mod_self,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod] using h
  have hc := hmod.cancel_right_of_coprime D.coprime.gcd_eq_one
  have hb' : b < D.m := (D.offset_le hb).trans_lt D.u_lt
  have hbc' : B+C < D.m := hbc.trans_lt hb'
  have hh : b=B+C := by
    change b%D.m=(B+C)%D.m at hc
    simpa only [Nat.mod_eq_of_lt hb',Nat.mod_eq_of_lt hbc'] using hc
  have hmul := Nat.mul_le_mul_right D.m (show 2≤n+l by omega)
  have := D.m_pos
  rw [hh] at heq
  omega

theorem atoms : D.source.atoms=D.generators := by
  ext x
  rw [D.source.mem_atoms_iff]
  constructor
  · intro hx
    exact D.source.atom_mem_of_generates rfl hx
  · intro hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact D.generator_atom b hb

theorem embeddingDimension : D.source.embeddingDimension=D.q+2 := by
  unfold NumericalSemigroup.embeddingDimension
  rw [D.atoms,generators,Finset.card_image_of_injective _ D.generator_injective,D.offsets_card]

theorem maxAtom : D.source.maxAtom=D.m+D.u*D.d := by
  apply Nat.le_antisymm
  · have hh : D.source.maxAtom∈D.generators := by
      rw [← D.atoms]
      exact Finset.max'_mem _ _
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hh
    rw [← he]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right D.d (D.offset_le hb)) D.m
  · exact D.source.atom_le_maxAtom (D.atoms ▸ D.generator_mem D.u (by simp))

theorem width : D.source.width=D.d*D.u := by
  unfold NumericalSemigroup.width
  rw [D.maxAtom,D.multiplicity,Nat.add_sub_cancel_left,Nat.mul_comm]
end Data
end NSP14.Endpoint
