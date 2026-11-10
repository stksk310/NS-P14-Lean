module

public import NSP14.Semigroup.TerminalCoordinates

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def jumpGSpace (s : ℕ) : Submodule k (S.TangentAlgebra k) :=
  (Finsupp.supported k k {t : S.carrier | S.Terminal t.val ∧ s ≤ S.jump t.val}).comap
    (S.tangentCoordinates k).toLinearMap

omit [Nontrivial k] in
theorem initial_mem_jumpGSpace (s : ℕ) (t : S.carrier)
    (ht : S.Terminal t.val) (hs : s ≤ S.jump t.val) :
    S.initialMonomial k t ∈ S.jumpGSpace k s := by
  change S.tangentCoordinates k _ ∈ Finsupp.supported k k _
  rw [S.tangentCoordinates_initial, Finsupp.mem_supported']
  intro y hy
  have hne : t ≠ y := by intro he; subst y; exact hy ⟨ht,hs⟩
  simp [hne]

omit [Nontrivial k] in
theorem tangent_expansion (a : S.TangentAlgebra k) :
    (S.tangentCoordinates k a).sum (fun t c => c • S.initialMonomial k t) = a := by
  have he := (S.tangentBasis k).linearCombination_repr a
  change ((S.tangentBasis k).repr a).sum (fun t c => c • S.tangentBasis k t) = a at he
  have hr : (S.tangentBasis k).repr a = S.tangentCoordinates k a := by
    simp [tangentBasis, Module.Basis.map]
  simpa only [S.tangentBasis_eq_initial, hr] using he

theorem terminal_add_of_live (t g : S.carrier) (ht : S.Terminal t.val)
    (hl : S.order (t.val+g.val) = S.order t.val + S.order g.val) :
    S.Terminal (t.val+g.val) := by
  have hm := S.jump_le_of_live_base t.property g.property hl
  have hb := S.terminal_jump ht
  refine ⟨S.add_mem t.property g.property, ?_⟩
  unfold jump at hm hb
  omega

theorem initial_mul_mem_jumpGSpace (s : ℕ) (g t : S.carrier)
    (ht : S.Terminal t.val) (hs : s ≤ S.jump t.val) :
    S.initialMonomial k g * S.initialMonomial k t ∈ S.jumpGSpace k s := by
  by_cases hl : S.order (t.val+g.val) = S.order t.val + S.order g.val
  · rw [mul_comm, S.initialMonomial_mul_live k t g hl]
    exact S.initial_mem_jumpGSpace k s (t+g) (S.terminal_add_of_live t g ht hl)
      (hs.trans (S.jump_le_of_live_base t.property g.property hl))
  · have ho := S.order_add t.property g.property
    rw [mul_comm, (S.initialMonomial_mul_eq_zero_iff k t g).2 (by omega)]
    exact (S.jumpGSpace k s).zero_mem

theorem jumpGSpace_mul (s : ℕ) (r a : S.TangentAlgebra k) (ha : a ∈ S.jumpGSpace k s) :
    r*a ∈ S.jumpGSpace k s := by
  have hs : ∀ t ∈ (S.tangentCoordinates k a).support, S.Terminal t.val ∧ s ≤ S.jump t.val :=
    (Finsupp.mem_supported k _).1 ha
  rw [← S.tangent_expansion k r, Finsupp.sum, Finset.sum_mul]
  apply (S.jumpGSpace k s).sum_mem
  intro g _
  rw [← S.tangent_expansion k a, Finsupp.sum, Finset.mul_sum]
  apply (S.jumpGSpace k s).sum_mem
  intro t ht
  simpa only [smul_mul_assoc, mul_smul_comm] using
    (S.jumpGSpace k s).smul_mem (S.tangentCoordinates k a t)
      ((S.jumpGSpace k s).smul_mem (S.tangentCoordinates k r g)
        (S.initial_mul_mem_jumpGSpace k s g t (hs t ht).1 (hs t ht).2))

/-- Descending jump filtration on the actual x-kernel, with the actual S₀ action. -/
noncomputable def descendingJump (s : ℕ) : Submodule (S.PolynomialRing k) ((S.xMultiply k).ker) where
  carrier := {a | a.val ∈ S.jumpGSpace k s}
  zero_mem' := (S.jumpGSpace k s).zero_mem
  add_mem' := (S.jumpGSpace k s).add_mem
  smul_mem' p a ha := S.jumpGSpace_mul k s (S.polynomialToG k p) a.val ha

theorem mem_descendingJump (s : ℕ) (a : (S.xMultiply k).ker) :
    a ∈ S.descendingJump k s ↔
      ∀ t : S.carrier, ¬(S.Terminal t.val ∧ s ≤ S.jump t.val) →
        S.tangentCoordinates k a.val t = 0 := by
  change S.tangentCoordinates k a.val ∈ Finsupp.supported k k _ ↔ _
  exact Finsupp.mem_supported' k _

theorem descendingJump_antitone : Antitone (S.descendingJump k) := by
  intro s t hst a ha
  rw [S.mem_descendingJump] at ha ⊢
  intro x hx
  apply ha x
  intro ht
  exact hx ⟨ht.1,hst.trans ht.2⟩

/-- The ascending support condition in the actual quotient A. -/
noncomputable def jumpASpace (s : ℕ) : Submodule k (S.HeadAlgebra k) :=
  (Finsupp.supported k k {h : S.HeadExponent |
    h.val.val ∉ S.aperySet ∧ S.jump (h.val.val-S.multiplicity) ≤ s}).comap
      (S.headQuotientEquiv k).toLinearMap

theorem head_mem_jumpASpace (s : ℕ) (h : S.carrier) (hn : h.val ∉ S.aperySet)
    (hs : S.jump (h.val-S.multiplicity) ≤ s) :
    S.headMonomial k h ∈ S.jumpASpace k s := by
  change S.headQuotientEquiv k _ ∈ Finsupp.supported k k _
  rw [Finsupp.mem_supported']
  intro y hy
  rw [S.headMonomial_coordinates]
  have hne : h ≠ y.val := by intro he; subst h; exact hy ⟨hn,hs⟩
  simp [hne]

theorem head_mul_mem_jumpASpace (s : ℕ) (g h : S.HeadExponent)
    (hn : h.val.val ∉ S.aperySet) (hs : S.jump (h.val.val-S.multiplicity) ≤ s) :
    S.headBasis k g * S.headBasis k h ∈ S.jumpASpace k s := by
  rw [← S.headMonomial_eq_basis k g, ← S.headMonomial_eq_basis k h]
  by_cases hl : S.order (g.val.val+h.val.val) = S.order g.val.val+S.order h.val.val
  · rw [S.headMonomial_mul_live k g.val h.val hl]
    by_cases hh : S.XHead (g.val.val+h.val.val)
    · obtain ⟨t,ht,he⟩ := S.head_predecessor ⟨h.property,hn⟩
      have ht' : h.val.val-S.multiplicity=t := by omega
      have hsum : (g.val+h.val).val-S.multiplicity=t+g.val.val := by
        change g.val.val+h.val.val-S.multiplicity=t+g.val.val
        omega
      apply S.head_mem_jumpASpace k s _ (S.nonapery_add g.val h.val hn)
      rw [hsum]
      rw [ht'] at hs
      apply (S.jump_le_of_live_head ht.1 g.val.property ?_).trans hs
      have he' : t+g.val.val+S.multiplicity = g.val.val+h.val.val := by omega
      rw [he', ← he]
      omega
    · rw [S.headMonomial_zero_of_not_head k (g.val+h.val) hh]
      exact (S.jumpASpace k s).zero_mem
  · have ho := S.order_add g.val.property h.val.property
    rw [S.headMonomial_mul_dead k g.val h.val (by omega)]
    exact (S.jumpASpace k s).zero_mem

theorem jumpASpace_mul (s : ℕ) (r a : S.HeadAlgebra k) (ha : a ∈ S.jumpASpace k s) :
    r*a ∈ S.jumpASpace k s := by
  have hs : ∀ h ∈ (S.headQuotientEquiv k a).support,
      h.val.val ∉ S.aperySet ∧ S.jump (h.val.val-S.multiplicity) ≤ s :=
    (Finsupp.mem_supported k _).1 ha
  rw [← S.head_expansion k r, Finsupp.sum, Finset.sum_mul]
  apply (S.jumpASpace k s).sum_mem
  intro g _
  rw [← S.head_expansion k a, Finsupp.sum, Finset.mul_sum]
  apply (S.jumpASpace k s).sum_mem
  intro h hh
  simpa only [smul_mul_assoc, mul_smul_comm] using
    (S.jumpASpace k s).smul_mem (S.headQuotientEquiv k a h)
      ((S.jumpASpace k s).smul_mem (S.headQuotientEquiv k r g)
        (S.head_mul_mem_jumpASpace k s g h (hs h hh).1 (hs h hh).2))

/-- Ascending jump filtration on the actual N ideal, over the same S₀. -/
noncomputable def ascendingJump (s : ℕ) :
    Submodule (S.PolynomialRing k) ((S.nonAperyIdeal k).restrictScalars k) where
  carrier := {a | a.val ∈ S.jumpASpace k s}
  zero_mem' := (S.jumpASpace k s).zero_mem
  add_mem' := (S.jumpASpace k s).add_mem
  smul_mem' p a ha := S.jumpASpace_mul k s (S.polynomialToA k p) a.val ha

theorem mem_ascendingJump (s : ℕ) (a : (S.nonAperyIdeal k).restrictScalars k) :
    a ∈ S.ascendingJump k s ↔
      ∀ h : S.HeadExponent, ¬(h.val.val ∉ S.aperySet ∧ S.jump (h.val.val-S.multiplicity) ≤ s) →
        S.headQuotientEquiv k a.val h = 0 := by
  change S.headQuotientEquiv k a.val ∈ Finsupp.supported k k _ ↔ _
  exact Finsupp.mem_supported' k _

theorem ascendingJump_monotone : Monotone (S.ascendingJump k) := by
  intro s t hst a ha
  rw [S.mem_ascendingJump] at ha ⊢
  intro h hh
  apply ha h
  intro hs
  exact hh ⟨hs.1,hs.2.trans hst⟩

end NSP14.NumericalSemigroup
