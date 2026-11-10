module

public import NSP14.Semigroup.AperyGrading

@[expose] public section

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup)

/-- Numerical labels of a dead multiplication-by-m arrow. -/
def Terminal (x : ℕ) : Prop := x ∈ S ∧ S.order x + 1 < S.order (x + S.multiplicity)

/-- Numerical labels with no live incoming multiplication-by-m arrow. -/
def XHead (y : ℕ) : Prop := y ∈ S ∧
  ¬ ∃ x ∈ S, y = x + S.multiplicity ∧ S.order y = S.order x + 1

def NonAperyHead (y : ℕ) : Prop := S.XHead y ∧ y ∉ S.aperySet

noncomputable def jump (x : ℕ) : ℕ := S.order (x + S.multiplicity) - S.order x

theorem terminal_iff_head (x : ℕ) : S.Terminal x ↔ S.NonAperyHead (x + S.multiplicity) := by
  constructor
  · rintro ⟨hx, horder⟩
    refine ⟨⟨S.add_mem hx S.multiplicity_mem, ?_⟩, ?_⟩
    · rintro ⟨y, hy, heq, hlive⟩
      have hxy : x = y := Nat.add_right_cancel heq
      subst y
      omega
    · intro ha
      exact S.apery_no_predecessor ha ⟨x, hx, rfl⟩
  · intro hy
    have hp : ∃ y ∈ S, x + S.multiplicity = y + S.multiplicity := by
      by_contra hn
      exact hy.2 ((S.mem_apery_iff_no_predecessor hy.1.1).mpr hn)
    obtain ⟨y, hymem, heq⟩ := hp
    have hxy : x = y := Nat.add_right_cancel heq
    subst y
    refine ⟨hymem, ?_⟩
    have hle := S.order_add_multiplicity hymem
    have hne : S.order (x + S.multiplicity) ≠ S.order x + 1 := by
      intro h
      exact hy.1.2 ⟨x, hymem, rfl, h⟩
    omega

theorem head_predecessor {y : ℕ} (hy : S.NonAperyHead y) :
    ∃ x, S.Terminal x ∧ y = x + S.multiplicity := by
  have hp : ∃ x ∈ S, y = x + S.multiplicity := by
    by_contra hn
    exact hy.2 ((S.mem_apery_iff_no_predecessor hy.1.1).mpr hn)
  obtain ⟨x, hx, heq⟩ := hp
  refine ⟨x, (S.terminal_iff_head x).mpr ?_, heq⟩
  rwa [← heq]

theorem head_sub_terminal {y : ℕ} (hy : S.NonAperyHead y) : S.Terminal (y - S.multiplicity) := by
  obtain ⟨x, hx, heq⟩ := S.head_predecessor hy
  simpa [heq] using hx

/-- A bijection of actual numerical labels, not a global T≅N module isomorphism. -/
noncomputable def terminalHeadEquiv : {x // S.Terminal x} ≃ {y // S.NonAperyHead y} where
  toFun x := ⟨x.val + S.multiplicity, (S.terminal_iff_head x.val).mp x.property⟩
  invFun y := ⟨y.val - S.multiplicity, S.head_sub_terminal y.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by
    apply Subtype.ext
    change (y.val - S.multiplicity) + S.multiplicity = y.val
    obtain ⟨x, hx, heq⟩ := S.head_predecessor y.property
    omega

theorem terminal_pos {x : ℕ} (hx : S.Terminal x) : 0 < x := by
  by_contra h
  have hx0 : x = 0 := by omega
  have ho := hx.2
  rw [hx0, zero_add, S.order_zero, S.order_multiplicity] at ho
  omega

theorem terminal_jump {x : ℕ} (hx : S.Terminal x) : 2 ≤ S.jump x := by
  unfold jump
  have := hx.2
  omega

theorem terminal_head_degree {x : ℕ} (hx : S.Terminal x) : 3 ≤ S.order (x + S.multiplicity) := by
  have hpos := S.order_pos hx.1 (S.terminal_pos hx)
  have := hx.2
  omega

/-- A live base action makes the numerical jump nondecreasing. -/
theorem jump_le_of_live_base {x g : ℕ} (hx : x ∈ S) (hg : g ∈ S)
    (hlive : S.order (x + g) = S.order x + S.order g) : S.jump x ≤ S.jump (x + g) := by
  have h1 := S.order_add (S.add_mem hx S.multiplicity_mem) hg
  have h2 := S.order_add_multiplicity hx
  have h3 := S.order_add_multiplicity (S.add_mem hx hg)
  rw [show x + S.multiplicity + g = x + g + S.multiplicity by omega] at h1
  unfold jump
  omega

/-- A live head action makes the numerical jump nonincreasing. -/
theorem jump_le_of_live_head {x g : ℕ} (hx : x ∈ S) (hg : g ∈ S)
    (hlive : S.order (x + g + S.multiplicity) = S.order (x + S.multiplicity) + S.order g) :
    S.jump (x + g) ≤ S.jump x := by
  have h1 := S.order_add hx hg
  have h2 := S.order_add_multiplicity hx
  have h3 := S.order_add_multiplicity (S.add_mem hx hg)
  unfold jump
  omega

/-- Equal-jump labels have matching live actions; no global matching is asserted. -/
theorem live_iff_of_equal_jump {x g : ℕ} (hx : x ∈ S) (hg : g ∈ S)
    (hjump : S.jump (x + g) = S.jump x) :
    (S.order (x + g) = S.order x + S.order g) ↔
      S.order (x + g + S.multiplicity) = S.order (x + S.multiplicity) + S.order g := by
  have h1 := S.order_add_multiplicity hx
  have h2 := S.order_add_multiplicity (S.add_mem hx hg)
  unfold jump at hjump
  omega

end NSP14.NumericalSemigroup
