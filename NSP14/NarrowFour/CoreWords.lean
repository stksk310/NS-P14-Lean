module
public import NSP14.Endpoint.TwoMonomial
public import NSP14.Endpoint.InternalSocleBasis
@[expose] public section
open scoped Classical
namespace NSP14.NarrowFour
variable (D : Endpoint.Data)

/-- The labels are genuine internal offsets, ordered in the original source. -/
def OrderedPair (a b : D.a) : Prop :=
  a.val < b.val ∧ ∀ c : D.a, c=a ∨ c=b

/-- Actual core point of the two-variable word. -/
def word (a b : D.a) (s t : ℕ) : D.corePoints :=
  s • D.coreGeneratorPoint (D.internalVariable a)+
    t • D.coreGeneratorPoint (D.internalVariable b)

def Standard (a b : D.a) (p : ℕ×ℕ) : Prop := D.CoreMinimal (word D a b p.1 p.2)

noncomputable def standardWords (a b : D.a) : Finset (ℕ×ℕ) :=
  ((Finset.range D.u).product (Finset.range D.u)).filter (Standard D a b)



set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

theorem ordered_pair_exists (hq : D.q=2) : ∃ a b : D.a, OrderedPair D a b := by
  obtain ⟨a,b,hne,he⟩ := Finset.card_eq_two.mp hq
  have ha : a∈D.a := by rw [he]; simp
  have hb : b∈D.a := by rw [he]; simp
  have hall (c : D.a) : c.val=a ∨ c.val=b := by
    let x : ℕ := c.val
    have hx : x∈D.a := c.property
    rw [he] at hx
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hx
  by_cases hab : a<b
  · refine ⟨⟨a,ha⟩,⟨b,hb⟩,hab,?_⟩
    intro c
    rcases hall c with hc|hc
    · exact Or.inl (Subtype.ext hc)
    · exact Or.inr (Subtype.ext hc)
  · refine ⟨⟨b,hb⟩,⟨a,ha⟩,(by change b<a; omega),?_⟩
    intro c
    rcases hall c with hc|hc
    · exact Or.inr (Subtype.ext hc)
    · exact Or.inl (Subtype.ext hc)

theorem word_coe (a b : D.a) (s t : ℕ) :
    (word D a b s t).val=(s+t,s*a.val+t*b.val) := by
  change (s • (1,a.val)+t • (1,b.val) : ℕ×ℕ)=_
  apply Prod.ext <;> simp

theorem word_degree (a b : D.a) (s t : ℕ) : D.coreDegree (word D a b s t)=s+t :=
  congrArg Prod.fst (word_coe D a b s t)

theorem word_offset (a b : D.a) (s t : ℕ) :
    D.coreOffset (word D a b s t)=s*a.val+t*b.val :=
  congrArg Prod.snd (word_coe D a b s t)

theorem word_succ_fst (a b : D.a) (s t : ℕ) :
    word D a b (s+1) t=D.coreGeneratorPoint (D.internalVariable a)+word D a b s t := by
  simp only [word,add_nsmul,one_nsmul]
  abel

theorem word_succ_snd (a b : D.a) (s t : ℕ) :
    word D a b s (t+1)=D.coreGeneratorPoint (D.internalVariable b)+word D a b s t := by
  simp only [word,add_nsmul,one_nsmul]
  abel

theorem word_add (a b : D.a) (s t x y : ℕ) :
    word D a b (s+x) (t+y)=word D a b s t+word D a b x y := by
  simp only [word,add_nsmul]
  abel

theorem word_injective (a b : D.a) (hab : a.val<b.val) :
    Function.Injective (fun p : ℕ×ℕ => word D a b p.1 p.2) := by
  rintro ⟨s,t⟩ ⟨x,y⟩ he
  have hn := congrArg D.coreDegree he
  have hB := congrArg D.coreOffset he
  simp only [word_degree,word_offset] at hn hB
  have hnQ : (s:ℤ)+t=x+y := by exact_mod_cast hn
  have hBQ : (s:ℤ)*a.val+t*b.val=x*a.val+y*b.val := by exact_mod_cast hB
  have hm : ((a.val:ℤ)-(b.val:ℤ))*((s:ℤ)-x)=0 := by nlinarith only [hnQ,hBQ]
  have hne : (a.val:ℤ)-(b.val:ℤ)≠0 := by omega
  have hx := (mul_eq_zero.mp hm).resolve_left hne
  apply Prod.ext <;> dsimp <;> omega

theorem minimal_add_left (p q : D.corePoints) (hm : D.CoreMinimal (p+q)) :
    D.CoreMinimal p := by
  by_contra hn
  rcases (D.core_not_minimal_iff_factor p).mp hn with ⟨r,hr⟩|⟨r,hr⟩
  · exact (D.core_not_minimal_iff_factor (p+q)).mpr
      (Or.inl ⟨r+q,by rw [hr]; abel⟩) hm
  · exact (D.core_not_minimal_iff_factor (p+q)).mpr
      (Or.inr ⟨r+q,by rw [hr]; abel⟩) hm

theorem standard_downward (a b : D.a) (p q : ℕ×ℕ)
    (hp : Standard D a b p) (hqp : q≤p) : Standard D a b q := by
  have he : word D a b p.1 p.2=word D a b q.1 q.2+
      word D a b (p.1-q.1) (p.2-q.2) := by
    rw [←word_add,Nat.add_sub_of_le hqp.1,Nat.add_sub_of_le hqp.2]
  change D.CoreMinimal (word D a b p.1 p.2) at hp
  change D.CoreMinimal (word D a b q.1 q.2)
  rw [he] at hp
  exact minimal_add_left D _ _ hp

theorem minimal_representation (a b : D.a) (hab : OrderedPair D a b)
    (p : D.CoreMinimalIndex) : ∃ s t : ℕ,p.val=word D a b s t := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hint := D.minimal_word_internal w (by rw [hw]; exact p.property)
  have rep : ∀ w : List D.Variables,(∀ c∈w,c.val∈D.a) →
      ∃ s t : ℕ,D.coreWord w=word D a b s t := by
    intro w
    induction w with
    | nil => exact fun _ => ⟨0,0,by simp [word]⟩
    | cons c w ih =>
      intro hint
      obtain ⟨s,t,hw⟩ := ih (fun e he => hint e (List.mem_cons_of_mem c he))
      rcases hab.2 ⟨c.val,hint c List.mem_cons_self⟩ with hc|hc
      · have hc' : c=D.internalVariable a := Subtype.ext (congrArg (fun x : D.a => x.val) hc)
        exact ⟨s+1,t,by rw [D.coreWord_cons,hw,hc']; exact (word_succ_fst D a b s t).symm⟩
      · have hc' : c=D.internalVariable b := Subtype.ext (congrArg (fun x : D.a => x.val) hc)
        exact ⟨s,t+1,by rw [D.coreWord_cons,hw,hc']; exact (word_succ_snd D a b s t).symm⟩
  obtain ⟨s,t,he⟩ := rep w hint
  exact ⟨s,t,hw.symm.trans he⟩

theorem standard_degree_lt (a b : D.a) (p : ℕ×ℕ) (hp : Standard D a b p) :
    p.1+p.2<D.u := by
  have h := D.coreMinimal_degree_lt ⟨word D a b p.1 p.2,hp⟩
  rwa [word_degree] at h

@[simp] theorem mem_standardWords (a b : D.a) (p : ℕ×ℕ) :
    p∈standardWords D a b ↔ Standard D a b p := by
  rw [standardWords,Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro hp
    have hd := standard_degree_lt D a b p hp
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_range.mpr (by omega)⟩,hp⟩

noncomputable def standardWordEquiv (a b : D.a) (hab : OrderedPair D a b) :
    ↑(standardWords D a b) ≃ D.CoreMinimalIndex :=
  Equiv.ofBijective (fun p => ⟨word D a b p.val.1 p.val.2,(mem_standardWords D a b p.val).mp p.property⟩)
    ⟨by
      intro p q he
      exact Subtype.ext (word_injective D a b hab.1 (congrArg Subtype.val he)),by
      intro p
      obtain ⟨s,t,he⟩ := minimal_representation D a b hab p
      refine ⟨⟨(s,t),(mem_standardWords D a b _).mpr (by change D.CoreMinimal (word D a b s t); rw [←he]; exact p.property)⟩,?_⟩
      exact Subtype.ext he.symm⟩

theorem coreP_card (k : Type) [Field k] (a b : D.a) (hab : OrderedPair D a b) :
    D.coreP k=(standardWords D a b).card := by
  rw [Endpoint.Data.coreP,Module.finrank_eq_card_basis (D.QCoreBasis k)]
  exact (Fintype.card_congr (standardWordEquiv D a b hab)).symm.trans (Fintype.card_coe _)

end NSP14.NarrowFour
