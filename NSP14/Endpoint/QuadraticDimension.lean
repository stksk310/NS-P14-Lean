module
public import NSP14.Endpoint.CoreHilbertSum
public import Mathlib.Data.Sym.NatCard
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem core_degree_two_pair (p : D.CoreMinimalIndex) (hp : D.coreDegree p.val=2) :
    ∃ b c : D.a,p.val=D.coreGeneratorPoint (D.internalVariable b)+D.coreGeneratorPoint (D.internalVariable c) := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hlen := D.coreWord_degree w
  rw [hw,hp] at hlen
  obtain ⟨b,c,hbc⟩ := List.length_eq_two.mp hlen.symm
  have hm : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2 := by rw [hw];exact p.property
  have hb := D.minimal_word_internal w hm b (by simp [hbc])
  have hc := D.minimal_word_internal w hm c (by simp [hbc])
  refine ⟨⟨b.val,hb⟩,⟨c.val,hc⟩,?_⟩
  rw [←hw,hbc,D.coreWord_cons,D.coreWord_cons,D.coreWord_nil,add_zero]
  rfl

abbrev QuadraticIndex := {p : D.CoreMinimalIndex // D.coreDegree p.val=2}

noncomputable def quadraticPair (p : D.QuadraticIndex) : D.a×D.a :=
  ⟨(D.core_degree_two_pair p.val p.property).choose,
    (D.core_degree_two_pair p.val p.property).choose_spec.choose⟩

theorem quadraticPair_point (p : D.QuadraticIndex) : p.val.val=
    D.coreGeneratorPoint (D.internalVariable (D.quadraticPair p).1)+
      D.coreGeneratorPoint (D.internalVariable (D.quadraticPair p).2) :=
  (D.core_degree_two_pair p.val p.property).choose_spec.choose_spec

noncomputable def quadraticLabel (p : D.QuadraticIndex) : Sym2 D.a := s((D.quadraticPair p).1,(D.quadraticPair p).2)

theorem quadraticLabel_injective : Function.Injective D.quadraticLabel := by
  intro a b h
  have he := Sym2.rel_iff.mp (Sym2.exact h)
  apply Subtype.ext
  apply Subtype.ext
  rw [D.quadraticPair_point a,D.quadraticPair_point b]
  rcases he with ⟨h1,h2⟩|⟨h1,h2⟩
  · rw [h1,h2]
  · rw [h1,h2,add_comm]

variable (k : Type) [Field k]

/-- The actual degree-two quotient basis is covered by unordered
pairs of actual internal atoms; relations can only reduce its size. -/
theorem coreHilbert_two_bound : D.coreHilbert k 2≤(D.q+1).choose 2 := by
  rw [D.coreHilbert_card]
  have h := Nat.card_le_card_of_injective D.quadraticLabel D.quadraticLabel_injective
  have hc : Nat.card D.a=D.q := by rw [Nat.card_eq_fintype_card,Fintype.card_coe];rfl
  rw [Sym2.natCard,hc] at h
  exact h
end NSP14.Endpoint.Data
