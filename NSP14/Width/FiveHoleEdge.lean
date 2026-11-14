module
public import NSP14.Width.FiveHoleCore
public import NSP14.Endpoint.CoreHilbertSum
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

/-- The two edge omissions are handled in the original coordinate direction. -/
theorem fiveHole_edge_degree_two_offset (hu : D.u=5)
    (ha : D.a={1,2,3} ∨ D.a={2,3,4}) (p : D.CoreMinimalIndex) (hp : D.coreDegree p.val=2) :
    D.coreOffset p.val=if D.a={1,2,3} then 4 else 6 := by
  obtain ⟨w,hw⟩ := D.exists_coreWord p.val
  have hm : D.CoreMinimal (D.coreWord w) := by rw [hw]; exact p.property
  have hd := D.coreWord_degree w
  rw [hw,hp] at hd
  have hwlen : w.length=2 := hd.symm
  have hint := D.minimal_word_internal w hm
  have hmissing := D.minimal_prefix_not_internal w hm 2 (by decide) (by omega)
  rw [List.take_of_length_le (by omega),hw,hu] at hmissing
  have hn0 : D.coreOffset p.val%5≠0 := by
    intro hz
    have hmod : D.coreOffset (D.coreWord (w.take 0))%D.u=
        D.coreOffset (D.coreWord (w.take 2))%D.u := by
      rw [List.take_zero,D.coreWord_nil,map_zero,Nat.zero_mod,
        List.take_of_length_le (by omega),hw,hu,hz]
    have he := D.minimal_prefix_eq w 0 2 (by omega) (by omega) hmod hm
    omega
  obtain ⟨b,c,hbc⟩ := List.length_eq_two.mp hwlen
  have hb : b.val∈D.a := hint b (by rw [hbc]; simp)
  have hc : c.val∈D.a := hint c (by rw [hbc]; simp)
  have hB : D.coreOffset p.val=b.val+c.val := by
    rw [←hw,hbc,D.coreWord_offset]
    simp
  rcases ha with ha|ha
  · have hb' : b.val=1 ∨ b.val=2 ∨ b.val=3 := by
      simpa only [ha,Finset.mem_insert,Finset.mem_singleton] using hb
    have hc' : c.val=1 ∨ c.val=2 ∨ c.val=3 := by
      simpa only [ha,Finset.mem_insert,Finset.mem_singleton] using hc
    rw [ha] at hmissing
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hmissing
    rw [ite_eq_left ha]
    omega
  · have hn : D.a≠{1,2,3} := by
      intro he
      have hh : (4:ℕ)∈D.a := by rw [ha]; simp
      rw [he] at hh
      norm_num at hh
    have hb' : b.val=2 ∨ b.val=3 ∨ b.val=4 := by
      simpa only [ha,Finset.mem_insert,Finset.mem_singleton] using hb
    have hc' : c.val=2 ∨ c.val=3 ∨ c.val=4 := by
      simpa only [ha,Finset.mem_insert,Finset.mem_singleton] using hc
    rw [ha] at hmissing
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hmissing
    rw [ite_eq_right hn]
    omega

variable (k : Type) [Field k]
theorem fiveHole_edge_coreP (hq : D.q=3) (hu : D.u=5)
    (ha : D.a={1,2,3} ∨ D.a={2,3,4}) : D.coreP k ≤ 5 := by
  have h2 : D.coreHilbert k 2 ≤ 1 := by
    rw [D.coreHilbert_card,Nat.card_eq_fintype_card]
    apply Fintype.card_le_one_iff.mpr
    intro p q
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact p.property.trans q.property.symm
    · exact (D.fiveHole_edge_degree_two_offset hu ha p.val p.property).trans
        (D.fiveHole_edge_degree_two_offset hu ha q.val q.property).symm
  have ht (n : ℕ) (hn : 3 ≤ n) : D.coreHilbert k n=0 := by
    rw [D.coreHilbert_card]
    have : IsEmpty {p : D.CoreMinimalIndex // D.coreDegree p.val=n} := ⟨by
      intro p
      have hd := D.fiveHole_minimal_degree hq hu p.val
      rw [p.property] at hd
      omega⟩
    rw [Nat.card_eq_fintype_card,Fintype.card_of_isEmpty]
  have hs := D.coreHilbert_sum k
  rw [hu] at hs
  norm_num [Finset.sum_range_succ,D.coreHilbert_zero,D.coreHilbert_one,hq,ht 3 (by decide),ht 4 (by decide)] at hs
  omega
end NSP14.Endpoint.Data
