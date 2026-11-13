module
public import NSP14.Additive.Sumset
public import NSP14.Endpoint.Volume
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical Pointwise
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)
instance residueModulusNeZero : NeZero D.u := ⟨Nat.ne_of_gt D.u_pos⟩
/-- The same normalized offsets as the actual core, not their physical d-multiples. -/
def residueAlphabet : Finset (ZMod D.u) := insert 0 (D.a.image (fun a : ℕ => (a : ZMod D.u)))
@[simp] theorem zero_mem_residueAlphabet : 0 ∈ D.residueAlphabet := Finset.mem_insert_self _ _
theorem offsets_image_residueAlphabet : D.offsets.image (fun a : ℕ => (a : ZMod D.u)) = D.residueAlphabet := by
  simp [offsets,residueAlphabet]
theorem residueAlphabet_card : D.residueAlphabet.card = D.q+1 := by
  have hinj : Set.InjOn (fun a : ℕ => (a : ZMod D.u)) D.a := by
    intro a ha b hb he
    have hh := congrArg ZMod.val he
    rwa [ZMod.val_natCast_of_lt (D.a_lt a ha),ZMod.val_natCast_of_lt (D.a_lt b hb)] at hh
  have hn : (0 : ZMod D.u) ∉ D.a.image (fun a : ℕ => (a : ZMod D.u)) := by
    rintro hh
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hh
    have hv := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (D.a_lt a ha),ZMod.val_zero] at hv
    have hp := D.a_pos a ha
    omega
  rw [residueAlphabet,Finset.card_insert_of_notMem hn,Finset.card_image_iff.mpr hinj]
  rfl

theorem corePoint_residue_mem (p : D.corePoints) :
    (D.coreOffset p : ZMod D.u) ∈ NSP14.Additive.iteratedSum D.residueAlphabet (D.coreDegree p) := by
  change (p.val.2 : ZMod D.u) ∈ NSP14.Additive.iteratedSum D.residueAlphabet p.val.1
  apply AddSubmonoid.closure_induction
    (motive := fun a _ => (a.2 : ZMod D.u) ∈ NSP14.Additive.iteratedSum D.residueAlphabet a.1)
    ?_ ?_ ?_ p.property
  · rintro a ⟨b,rfl⟩
    rw [NSP14.Additive.iteratedSum_one,←D.offsets_image_residueAlphabet]
    exact Finset.mem_image_of_mem _ b.property
  · simp only [Prod.snd_zero,Nat.cast_zero,Prod.fst_zero,NSP14.Additive.iteratedSum_zero,
      Finset.mem_singleton]
  · intro a b _ _ ha hb
    change ((a.2+b.2 : ℕ) : ZMod D.u) ∈ NSP14.Additive.iteratedSum D.residueAlphabet (a.1+b.1)
    rw [Nat.cast_add,NSP14.Additive.iteratedSum_add]
    exact Finset.mem_add.mpr ⟨_,ha,_,hb,rfl⟩

theorem residueAlphabet_iterated_core (n : ℕ) (r : ZMod D.u) :
    r ∈ NSP14.Additive.iteratedSum D.residueAlphabet n ↔
      ∃ p : D.corePoints, D.coreDegree p = n ∧ (D.coreOffset p : ZMod D.u) = r := by
  constructor
  · induction n generalizing r with
    | zero =>
      intro hr
      have he : r = 0 := Finset.mem_singleton.mp hr
      exact ⟨0,rfl,by simpa only [map_zero,Nat.cast_zero] using he.symm⟩
    | succ n ih =>
      intro hr
      obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hr
      obtain ⟨p,hp,hpr⟩ := ih x hx
      rw [←D.offsets_image_residueAlphabet] at hy
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hy
      refine ⟨p+D.coreGeneratorPoint ⟨b,hb⟩,?_,?_⟩
      · change D.coreDegree p+1=n+1
        rw [hp]
      · change ((D.coreOffset p+b : ℕ) : ZMod D.u)=x+b
        rw [Nat.cast_add,hpr]
  · rintro ⟨p,hp,rfl⟩
    rw [←hp]
    exact D.corePoint_residue_mem p
end NSP14.Endpoint.Data
