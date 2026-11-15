module
public import NSP14.Width.EdgeHoleMinor
public import NSP14.Width.DenseResources
public import NSP14.Endpoint.CoreHilbertSum
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

theorem minimal_degree_two_offset_bounds (p : D.CoreMinimalIndex) (hp : D.coreDegree p.val=2) :
    2 ≤ D.coreOffset p.val ∧ D.coreOffset p.val+2 ≤ 2*D.u := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hm : D.CoreMinimal (D.coreWord w) := by rw [hw]; exact p.property
  have hd := D.coreWord_degree w
  rw [hw,hp] at hd
  obtain ⟨b,c,hbc⟩ := List.length_eq_two.mp hd.symm
  have hint := D.minimal_word_internal w hm
  have hb := hint b (by rw [hbc]; simp)
  have hc := hint c (by rw [hbc]; simp)
  have hb0 := D.a_pos b.val hb
  have hc0 := D.a_pos c.val hc
  have hbLt := D.a_lt b.val hb
  have hcLt := D.a_lt c.val hc
  have hB : D.coreOffset p.val=b.val+c.val := by
    rw [←hw,hbc,D.coreWord_offset]
    simp
  omega

namespace OneHole
variable {D} (H : D.OneHole)

theorem block_false_card : (H.block false).card=H.h-1 := by
  have he : (H.block false).image (fun b : D.a => b.val)=Finset.Ioo 0 H.h := by
    ext n
    constructor
    · rintro hn
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Ioo.mpr ⟨D.a_pos b.val b.property,
        (H.side_false_iff b).mp (Finset.mem_filter.mp hb).2⟩
    · intro hn
      obtain ⟨hn0,hnh⟩ := Finset.mem_Ioo.mp hn
      have hna : n∈D.a := by
        rw [H.alphabet]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_Ioo.mpr ⟨hn0,hnh.trans H.lt⟩,by simp only [Finset.mem_singleton]; omega⟩
      refine Finset.mem_image.mpr ⟨⟨n,hna⟩,?_,rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,(H.side_false_iff _).mpr hnh⟩
  rw [←Finset.card_image_of_injective _ (Subtype.val_injective : Function.Injective (fun b : D.a => b.val)),he,Nat.card_Ioo,Nat.sub_zero]

theorem block_true_card : (H.block true).card=D.u-H.h-1 := by
  have he : (H.block true).image (fun b : D.a => b.val)=Finset.Ioo H.h D.u := by
    ext n
    constructor
    · intro hn
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hn
      exact Finset.mem_Ioo.mpr ⟨(H.side_true_iff b).mp (Finset.mem_filter.mp hb).2,D.a_lt b.val b.property⟩
    · intro hn
      obtain ⟨hnh,hnu⟩ := Finset.mem_Ioo.mp hn
      have hna : n∈D.a := by
        rw [H.alphabet]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_Ioo.mpr ⟨H.pos.trans hnh,hnu⟩,by simp only [Finset.mem_singleton]; omega⟩
      refine Finset.mem_image.mpr ⟨⟨n,hna⟩,?_,rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,(H.side_true_iff _).mpr hnh⟩
  rw [←Finset.card_image_of_injective _ (Subtype.val_injective : Function.Injective (fun b : D.a => b.val)),he,Nat.card_Ioo]

variable (k : Type) [Field k]
theorem resources (hu : D.u=D.q+2) : D.coreP k ≤ D.q+3 ∧ D.actualR k=0 ∧ D.coreHeight ≤ 1 := by
  have hq : 2 ≤ D.q := D.q_two
  obtain ⟨_,hp,_,hr,hh⟩ := D.dense_resources k 1 (by omega) (by omega)
  exact ⟨by omega,hr (by decide),hh⟩

theorem edge_degree_two_offset (hedge : H.h=1 ∨ H.h+1=D.u) (p : D.CoreMinimalIndex)
    (hp : D.coreDegree p.val=2) : D.coreOffset p.val=if H.h=1 then H.h+D.u else H.h := by
  have hB := D.one_missing_degree_two_offset H.h H.pos H.lt H.alphabet p hp
  have hbounds := D.minimal_degree_two_offset_bounds p hp
  rcases hedge with h1|h1
  · rw [ite_eq_left h1]
    omega
  · by_cases he : H.h=1
    · rw [ite_eq_left he]
      omega
    · rw [ite_eq_right he]
      omega

theorem edge_coreP (hu : D.u=D.q+2) (hedge : H.h=1 ∨ H.h+1=D.u) : D.coreP k ≤ D.q+2 := by
  dsimp only [q] at hu ⊢
  have h2 : D.coreHilbert k 2 ≤ 1 := by
    rw [D.coreHilbert_card,Nat.card_eq_fintype_card]
    apply Fintype.card_le_one_iff.mpr
    intro p q
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact p.property.trans q.property.symm
    · exact (H.edge_degree_two_offset hedge p.val p.property).trans
        (H.edge_degree_two_offset hedge q.val q.property).symm
  have ht (n : ℕ) (hn : 3 ≤ n) : D.coreHilbert k n=0 := by
    rw [D.coreHilbert_card]
    have : IsEmpty {p : D.CoreMinimalIndex // D.coreDegree p.val=n} := ⟨by
      intro p
      have hd := D.one_missing_degree hu p.val
      rw [p.property] at hd
      omega⟩
    rw [Nat.card_eq_fintype_card,Fintype.card_of_isEmpty]
  have hu3 : 3 ≤ D.u := by have := D.q_two; omega
  have hs := D.coreHilbert_sum k
  have hz : (∑ n∈Finset.range (D.u-3),D.coreHilbert k (3+n))=0 := by
    apply Finset.sum_eq_zero
    intro n _
    exact ht _ (by omega)
  rw [show D.u=3+(D.u-3) by omega,Finset.sum_range_add,hz,add_zero] at hs
  norm_num [Finset.sum_range_succ,D.coreHilbert_zero,D.coreHilbert_one] at hs
  dsimp only [q] at hs
  omega
end OneHole
end NSP14.Endpoint.Data
