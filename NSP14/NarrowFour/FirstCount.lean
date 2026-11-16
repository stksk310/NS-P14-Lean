module
public import NSP14.NarrowFour.Relations
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NarrowFour

/-- Inclusive triangle in the original exponent lattice. -/
def exponentTriangle (n : ℕ) : Finset (ℕ×ℕ) :=
  ((Finset.range (n+1)).product (Finset.range (n+1))).filter (fun p => p.1+p.2 ≤ n)

theorem mem_exponentTriangle (n : ℕ) (p : ℕ×ℕ) :
    p∈exponentTriangle n ↔ p.1+p.2 ≤ n := by
  rw [exponentTriangle,Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩,h⟩

theorem exponentTriangle_card (n : ℕ) : (exponentTriangle n).card=(n+2).choose 2 := by
  let f : (Σ s : Fin (n+1),Fin (s.val+1)) → ↑(exponentTriangle n) := fun p =>
    ⟨(p.1.val-p.2.val,p.2.val),(mem_exponentTriangle n _).mpr
      (by have := p.1.isLt;have := p.2.isLt;omega)⟩
  have hi : Function.Injective f := by
    rintro ⟨s,t⟩ ⟨x,y⟩ he
    have ht := congrArg (fun p : ↑(exponentTriangle n) => p.val.2) he
    have hs := congrArg (fun p : ↑(exponentTriangle n) => p.val.1) he
    change t.val=y.val at ht
    change s.val-t.val=x.val-y.val at hs
    have hS : s=x := Fin.ext (by have := t.isLt;have := y.isLt;omega)
    subst x
    have hT : t=y := Fin.ext ht
    subst y
    rfl
  have hs : Function.Surjective f := by
    intro p
    have hp := (mem_exponentTriangle n p.val).mp p.property
    refine ⟨⟨⟨p.val.1+p.val.2,by omega⟩,⟨p.val.2,show p.val.2<p.val.1+p.val.2+1 by omega⟩⟩,?_⟩
    apply Subtype.ext
    apply Prod.ext
    · dsimp [f];omega
    · rfl
  have hc := Fintype.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)
  rw [triangle_indices_card,Fintype.card_coe] at hc
  exact hc.symm

def positiveTriangle (h : ℕ) : Finset (ℕ×ℕ) :=
  (exponentTriangle h).filter (fun p => 0<p.1 ∧ 0<p.2)

theorem mem_positiveTriangle (h : ℕ) (p : ℕ×ℕ) :
    p∈positiveTriangle h ↔ 0<p.1 ∧ 0<p.2 ∧ p.1+p.2 ≤ h := by
  simp only [positiveTriangle,Finset.mem_filter,mem_exponentTriangle]
  omega

theorem positiveTriangle_card (h : ℕ) : (positiveTriangle h).card=h.choose 2 := by
  by_cases hh : 2 ≤ h
  · have he : positiveTriangle h=(exponentTriangle (h-2)).image (fun p => (p.1+1,p.2+1)) := by
      ext p
      rw [mem_positiveTriangle,Finset.mem_image]
      constructor
      · intro hp
        exact ⟨(p.1-1,p.2-1),(mem_exponentTriangle _ _).mpr (by omega),by
          apply Prod.ext <;> dsimp <;> omega⟩
      · rintro ⟨q,hq,rfl⟩
        have hq' := (mem_exponentTriangle _ _).mp hq
        dsimp
        omega
    rw [he,Finset.card_image_of_injective]
    · rw [exponentTriangle_card,show h-2+2=h by omega]
    · intro p q he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      apply Prod.ext <;> dsimp at * <;> omega
  · have he : positiveTriangle h=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have := (mem_positiveTriangle _ _).mp hp
      omega
    rw [he,Finset.card_empty,Nat.choose_eq_zero_of_lt (by omega)]

def axes (b c : ℕ) : Finset (ℕ×ℕ) :=
  (Finset.range b).image (fun s => (s,0)) ∪
    (Finset.range (c-1)).image (fun t => (0,t+1))

theorem mem_axes (b c : ℕ) (p : ℕ×ℕ) : p∈axes b c ↔
    (p.1<b ∧ p.2=0) ∨ (p.1=0 ∧ 0<p.2 ∧ p.2<c) := by
  rcases p with ⟨x,y⟩
  simp only [axes,Finset.mem_union,Finset.mem_image,Finset.mem_range,Prod.mk.injEq]
  constructor
  · rintro (⟨s,hs,h1,h2⟩|⟨t,ht,h1,h2⟩) <;> omega
  · rintro (⟨h1,h2⟩|⟨h1,h2,h3⟩)
    · exact Or.inl ⟨x,h1,rfl,by omega⟩
    · exact Or.inr ⟨y-1,by omega,by omega,by omega⟩

theorem axes_card (b c : ℕ) : (axes b c).card=b+(c-1) := by
  have hd : Disjoint ((Finset.range b).image (fun s : ℕ => (s,0)))
      ((Finset.range (c-1)).image (fun t : ℕ => (0,t+1))) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hp
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hq
    have hh := congrArg Prod.snd (hs.trans ht.symm)
    dsimp at hh
    omega
  rw [axes,Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h),
    Finset.card_image_of_injective _ (by
      intro p q h
      have hh := congrArg Prod.snd h
      dsimp at hh
      omega),Finset.card_range,Finset.card_range]

/-- The removed corner triangle; the guard is essential when k₀>h. -/
def removedTriangle (h A B : ℕ) : Finset (ℕ×ℕ) :=
  if A+B ≤ h then (exponentTriangle (h-(A+B))).image (fun p => (p.1+A,p.2+B)) else ∅

theorem removedTriangle_card (h A B : ℕ) :
    (removedTriangle h A B).card=if A+B ≤ h then (h-(A+B)+2).choose 2 else 0 := by
  unfold removedTriangle
  split_ifs
  · rw [Finset.card_image_of_injective]
    · exact exponentTriangle_card _
    · intro p q he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      apply Prod.ext <;> dsimp at * <;> omega
  · rfl

theorem mem_removedTriangle (h A B : ℕ) (p : ℕ×ℕ) :
    p∈removedTriangle h A B ↔ A ≤ p.1 ∧ B ≤ p.2 ∧ p.1+p.2 ≤ h := by
  unfold removedTriangle
  split_ifs with hh
  · rw [Finset.mem_image]
    constructor
    · rintro ⟨q,hq,rfl⟩
      have hq' := (mem_exponentTriangle _ _).mp hq
      dsimp
      omega
    · intro hp
      refine ⟨(p.1-A,p.2-B),(mem_exponentTriangle _ _).mpr (by omega),?_⟩
      apply Prod.ext <;> dsimp <;> omega
  · simp only [Finset.notMem_empty,false_iff]
    omega

variable (D : Endpoint.Data)
/-- Actual standard words and the excluded rectangle fit disjointly into axes plus mixed triangle. -/
theorem coreP_count_add (k : Type) [Field k] (_hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) :
    D.coreP k+(if D.u-b.val+a.val ≤ D.u/2 then
      (D.u/2-(D.u-b.val+a.val)+2).choose 2 else 0) ≤
        2*D.u-(D.u-b.val+a.val)-1+(D.u/2).choose 2 := by
  let h := D.u/2
  let A := D.u-b.val
  let B := a.val
  let R := removedTriangle h A B
  have hA : 0<A := by dsimp [A];have := D.a_lt _ b.property;omega
  have hB : 0<B := D.a_pos _ a.property
  have hne : a≠b := fun he => (ne_of_lt hab.1) (congrArg (fun x : D.a => x.val) he)
  have hd : Disjoint (standardWords D a b) R := by
    apply Finset.disjoint_left.mpr
    intro p hp hr
    have hs := (mem_standardWords D a b p).mp hp
    have hb := standard_relations_bound D a b hab.1 p.1 p.2 hs
    have hr' := (mem_removedTriangle h A B p).mp hr
    exact hb.2.2 ⟨hr'.1,hr'.2.1⟩
  have hi : standardWords D a b ∪ R ⊆ axes b.val (D.u-a.val) ∪ positiveTriangle h := by
    intro p hp
    rcases Finset.mem_union.mp hp with hp|hp
    · have hs := (mem_standardWords D a b p).mp hp
      have hb := standard_relations_bound D a b hab.1 p.1 p.2 hs
      by_cases ht : p.2=0
      · exact Finset.mem_union_left _ ((mem_axes _ _ p).mpr (Or.inl ⟨hb.1,ht⟩))
      by_cases hz : p.1=0
      · exact Finset.mem_union_left _ ((mem_axes _ _ p).mpr (Or.inr ⟨hz,by omega,hb.2.1⟩))
      have hm := standard_mixed_bound D a b hne p.1 p.2 (by omega) (by omega) hs
      exact Finset.mem_union_right _ ((mem_positiveTriangle _ p).mpr ⟨by omega,by omega,by dsimp [h];omega⟩)
    · have hr := (mem_removedTriangle h A B p).mp hp
      exact Finset.mem_union_right _ ((mem_positiveTriangle _ p).mpr ⟨by omega,by omega,hr.2.2⟩)
  have hc := (Finset.card_le_card hi).trans (Finset.card_union_le _ _)
  rw [Finset.card_union_of_disjoint hd,axes_card,positiveTriangle_card,
    removedTriangle_card,←coreP_card D k a b hab] at hc
  dsimp [R,h,A,B] at hc
  have ha := D.a_pos _ a.property
  have hb := D.a_lt _ b.property
  have hab' := hab.1
  omega

theorem first_count (k : Type) [Field k] (hq : D.q=2)
    (a b : D.a) (hab : OrderedPair D a b) :
    let h := D.u/2
    let k₀ := D.u-b.val+a.val
    let E := if k₀ ≤ h then (h-k₀+2).choose 2 else 0
    D.coreP k ≤ 2*D.u-k₀-1+h.choose 2-E ∧
    D.coreP k ≤ 2*D.u-h-2+h.choose 2 ∧ D.internalSigma k hq ≤ min (h+1) k₀ := by
  dsimp only
  have hc := coreP_count_add D k hq a b hab
  have hu : 3 ≤ D.u := by have h := D.q_add_one_le_u;omega
  have ha := D.a_pos _ a.property
  have hb := D.a_lt _ b.property
  have hab' := hab.1
  have he : D.u/2+1 ≤ D.u-b.val+a.val+
      (if D.u-b.val+a.val ≤ D.u/2 then (D.u/2-(D.u-b.val+a.val)+2).choose 2 else 0) := by
    split_ifs with hh
    · have hchoose : D.u/2-(D.u-b.val+a.val)+1 ≤
          (D.u/2-(D.u-b.val+a.val)+2).choose 2 := by
        have h := Nat.choose_succ_succ (D.u/2-(D.u-b.val+a.val)+1) 1
        simp only [Nat.choose_one_right] at h
        change (D.u/2-(D.u-b.val+a.val)+2).choose 2=
          (D.u/2-(D.u-b.val+a.val)+1)+(D.u/2-(D.u-b.val+a.val)+1).choose 2 at h
        omega
      omega
    · omega
  exact ⟨by omega,by omega,sigma_first_bounds D k hq a b hab⟩
end NSP14.NarrowFour
