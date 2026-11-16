module
public import NSP14.Width.DenseHeight
public import NSP14.Width.TripleCorePoint
public import Mathlib.Order.Interval.Finset.Nat
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

/-- The actual alphabet misses exactly one interior integer. -/
theorem one_missing_offset (hu : D.u=D.q+2) :
    ∃ h : ℕ,0<h ∧ h<D.u ∧ D.a=Finset.Ioo 0 D.u \ {h} := by
  have hs : D.a⊆Finset.Ioo 0 D.u := by
    intro b hb
    exact Finset.mem_Ioo.mpr ⟨D.a_pos b hb,D.a_lt b hb⟩
  have hc : (Finset.Ioo 0 D.u \ D.a).card=1 := by
    rw [Finset.card_sdiff_of_subset hs,Nat.card_Ioo]
    change D.u-0-1-D.q=1
    omega
  obtain ⟨h,hh⟩ := Finset.card_eq_one.mp hc
  have hm : h∈Finset.Ioo 0 D.u \ D.a := by rw [hh]; simp
  obtain ⟨hr,hn⟩ := Finset.mem_sdiff.mp hm
  obtain ⟨h0,hu'⟩ := Finset.mem_Ioo.mp hr
  refine ⟨h,h0,hu',?_⟩
  ext b
  constructor
  · intro hb
    exact Finset.mem_sdiff.mpr ⟨hs hb,by
      simp only [Finset.mem_singleton]
      intro he
      exact hn (he ▸ hb)⟩
  · intro hb
    obtain ⟨hb,hne⟩ := Finset.mem_sdiff.mp hb
    by_contra hn'
    have hm' : b∈Finset.Ioo 0 D.u \ D.a := Finset.mem_sdiff.mpr ⟨hb,hn'⟩
    rw [hh] at hm'
    exact hne hm'

/-- Original minimal words have degree at most two in the one-hole case. -/
theorem one_missing_degree (hu : D.u=D.q+2) (p : D.CoreMinimalIndex) :
    D.coreDegree p.val ≤ 2 := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hm : D.CoreMinimal (D.coreWord w) := by rw [hw]; exact p.property
  have hl := D.minimal_word_missing_bound w hm
  have hd := D.coreWord_degree w
  rw [hw] at hd
  omega

/-- Every degree-two surviving basis point lies over the actual missing residue. -/
theorem one_missing_degree_two_offset (h : ℕ) (h0 : 0<h) (_hh : h<D.u)
    (ha : D.a=Finset.Ioo 0 D.u \ {h}) (p : D.CoreMinimalIndex)
    (hp : D.coreDegree p.val=2) : D.coreOffset p.val=h ∨ D.coreOffset p.val=h+D.u := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hm : D.CoreMinimal (D.coreWord w) := by rw [hw]; exact p.property
  have hd := D.coreWord_degree w
  rw [hw,hp] at hd
  have hwlen : w.length=2 := hd.symm
  have hint := D.minimal_word_internal w hm
  have hmissing := D.minimal_prefix_not_internal w hm 2 (by decide) (by omega)
  rw [List.take_of_length_le (by omega),hw] at hmissing
  have hn0 : D.coreOffset p.val%D.u≠0 := by
    intro hz
    have hmod : D.coreOffset (D.coreWord (w.take 0))%D.u=
        D.coreOffset (D.coreWord (w.take 2))%D.u := by
      rw [List.take_zero,D.coreWord_nil,map_zero,Nat.zero_mod,
        List.take_of_length_le (by omega),hw,hz]
    have he := D.minimal_prefix_eq w 0 2 (by omega) (by omega) hmod hm
    omega
  have hr : D.coreOffset p.val%D.u=h := by
    by_contra hn
    apply hmissing
    rw [ha]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_Ioo.mpr ⟨by omega,Nat.mod_lt _ D.u_pos⟩,
      by simpa only [Finset.mem_singleton] using hn⟩
  obtain ⟨b,c,hbc⟩ := List.length_eq_two.mp hwlen
  have hb := hint b (by rw [hbc]; simp)
  have hc := hint c (by rw [hbc]; simp)
  have hbLt := D.a_lt b.val hb
  have hcLt := D.a_lt c.val hc
  have hB : D.coreOffset p.val=b.val+c.val := by
    rw [←hw,hbc,D.coreWord_offset]
    simp
  have hdiv := Nat.mod_add_div (D.coreOffset p.val) D.u
  have hdv : D.coreOffset p.val / D.u < 2 :=
    (Nat.div_lt_iff_lt_mul D.u_pos).mpr (by omega)
  have hquotNonneg : 0 ≤ D.coreOffset p.val / D.u := Nat.zero_le _
  have hquot : D.coreOffset p.val / D.u=0 ∨ D.coreOffset p.val / D.u=1 := by omega
  rcases hquot with hquot|hquot <;> rw [hr,hquot] at hdiv <;> simp only [mul_zero,mul_one,add_zero] at hdiv <;> omega
end NSP14.Endpoint.Data
