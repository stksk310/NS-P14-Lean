module

public import NSP14.Semigroup.LiveSplit

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- Direct prefix proof: every terminal jump is bounded by the actual top degree of Q. -/
theorem terminal_jump_upper {x : ℕ} (hx : S.Terminal x) : S.jump x ≤ S.qTopDegree := by
  let h : S.carrier := ⟨x + S.multiplicity, S.add_mem hx.1 S.multiplicity_mem⟩
  have h2 := S.terminal_jump hx
  have hbase := S.order_add_multiplicity hx.1
  have hdef : S.jump x = S.order h.val - S.order x := rfl
  by_cases hh : S.order h.val ≤ S.qTopDegree
  · omega
  have hc : S.qTopDegree + 1 ≤ S.order h.val := by omega
  obtain ⟨u, v, huv, hu, hv⟩ := S.order_live_split h (S.qTopDegree + 1) hc
  have hval : h.val = u.val + v.val := congrArg Subtype.val huv
  have hnot : u.val ∉ S.aperySet := by
    intro ha
    have hb := S.apery_order_le_top (⟨u, ha⟩ : S.AperyExponent)
    change S.order u.val ≤ S.qTopDegree at hb
    omega
  have hp : ∃ y ∈ S, u.val = y + S.multiplicity := by
    by_contra hn
    exact hnot ((S.mem_apery_iff_no_predecessor u.property).2 hn)
  obtain ⟨y, hy, heq⟩ := hp
  have hxval : x = y + v.val := by
    change x + S.multiplicity = u.val + v.val at hval
    omega
  have hsum := S.order_add hy v.property
  rw [← hxval] at hsum
  by_cases hy0 : y = 0
  · have hum : u.val = S.multiplicity := by omega
    have humord : S.order u.val = 1 := hum ▸ S.order_multiplicity
    omega
  · have hypos := S.order_pos hy (by omega)
    omega

theorem terminal_jump_bounds {x : ℕ} (hx : S.Terminal x) :
    2 ≤ S.jump x ∧ S.jump x ≤ S.qTopDegree := ⟨S.terminal_jump hx, S.terminal_jump_upper hx⟩

theorem no_terminal_of_top_le_one (h : S.qTopDegree ≤ 1) (x : ℕ) : ¬S.Terminal x := by
  intro hx
  have hb := S.terminal_jump_bounds hx
  omega

theorem no_terminal_of_deficit_zero (h : S.deficit = 0) (x : ℕ) : ¬S.Terminal x := by
  apply S.no_terminal_of_top_le_one
  have ht := S.qTopDegree_le_deficit
  omega

end NSP14.NumericalSemigroup
