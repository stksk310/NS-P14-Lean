module
public import NSP14.Endpoint.Corners
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint
variable (U : Set (ℕ×ℕ)) (hU : ∀ {a b},a∈U → a≤b → b∈U)

/-- Consecutive minimal points in increasing horizontal order. The
vertical order is necessarily strictly decreasing. -/
def AdjacentMinima (a b : ℕ×ℕ) : Prop := Minimal (·∈U) a ∧ Minimal (·∈U) b ∧
  a.1 < b.1 ∧ ∀ z,Minimal (·∈U) z → ¬(a.1 < z.1 ∧ z.1 < b.1)

theorem minimal_vertical_reverse {a b : ℕ×ℕ} (ha : Minimal (·∈U) a)
    (hb : Minimal (·∈U) b) (hab : a.1 < b.1) : b.2 < a.2 := by
  by_contra hn
  have he := hb.eq_of_le ha.prop (show a≤b from ⟨hab.le,by omega⟩)
  have hf := congrArg Prod.fst he
  omega

noncomputable def cornerAbove (c : {c | Corner U c}) : {b | Minimal (·∈U) b} :=
  let h := exists_minimal_le_of_wellFoundedLT (·∈U) (c.val.1,c.val.2+1) c.property.2.2
  ⟨h.choose,h.choose_spec.2⟩

include hU in
theorem cornerAbove_snd (c : {c | Corner U c}) : (cornerAbove U c).val.2=c.val.2+1 := by
  have hle := (exists_minimal_le_of_wellFoundedLT (·∈U) (c.val.1,c.val.2+1) c.property.2.2).choose_spec.1
  change (cornerAbove U c).val≤(c.val.1,c.val.2+1) at hle
  by_contra he
  exact c.property.1 (hU (cornerAbove U c).property.prop ⟨hle.1,by have := hle.2;omega⟩)

include hU in
theorem corner_adjacent (c : {c | Corner U c}) :
    AdjacentMinima U (cornerAbove U c).val (cornerRight U c).val := by
  have hle := (exists_minimal_le_of_wellFoundedLT (·∈U) (c.val.1,c.val.2+1) c.property.2.2).choose_spec.1
  change (cornerAbove U c).val≤(c.val.1,c.val.2+1) at hle
  have hL := hle.1
  have hr := cornerRight_fst U hU c
  refine ⟨(cornerAbove U c).property,(cornerRight U c).property,by omega,?_⟩
  intro z hz ⟨hzl,hzr⟩
  have hzK := minimal_vertical_reverse U (cornerAbove U c).property hz hzl
  have haK := cornerAbove_snd U hU c
  exact c.property.1 (hU hz.prop ⟨by omega,by omega⟩)

include hU in
theorem adjacent_corner {a b : ℕ×ℕ} (hab : AdjacentMinima U a b) :
    Corner U (b.1-1,a.2-1) := by
  have hL := hab.2.2.1
  have hK := minimal_vertical_reverse U hab.1 hab.2.1 hL
  have hA : 1≤b.1 := by omega
  have hB : 1≤a.2 := by omega
  refine ⟨?_,?_,?_⟩
  · intro hc
    obtain ⟨z,hzle,hz⟩ := exists_minimal_le_of_wellFoundedLT (·∈U) (b.1-1,a.2-1) hc
    have haz : a.1 < z.1 := by
      by_contra hn
      have he := hab.1.eq_of_le hz.prop (show z≤a from ⟨by omega,by have := hzle.2;omega⟩)
      have heK := congrArg Prod.snd he
      have := hzle.2
      omega
    exact hab.2.2.2 z hz ⟨haz,by have := hzle.1;omega⟩
  · apply hU hab.2.1.prop
    exact ⟨by dsimp;omega,by dsimp;omega⟩
  · apply hU hab.1.prop
    exact ⟨by dsimp;omega,by dsimp;omega⟩

include hU in
theorem corner_adjacent_formula (c : {c | Corner U c}) :
    c.val=((cornerRight U c).val.1-1,(cornerAbove U c).val.2-1) := by
  rw [cornerRight_fst U hU,cornerAbove_snd U hU]
  simp
end NSP14.Endpoint
