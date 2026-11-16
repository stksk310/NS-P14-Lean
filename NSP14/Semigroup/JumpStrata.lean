module

public import NSP14.Semigroup.JumpAction

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def descendingJumpMonomial (s : ℕ) (t : S.JumpExponent s) : S.descendingJump k s :=
  ⟨S.terminalMonomial k t.val,
    S.initial_mem_jumpGSpace k s t.val.val t.val.property (le_of_eq t.property.symm)⟩

noncomputable def ascendingJumpMonomial (s : ℕ) (t : S.JumpExponent s) : S.ascendingJump k s :=
  ⟨S.nonAperyMonomial k (S.terminalHeadExponentEquiv t.val), by
    apply S.head_mem_jumpASpace k s _ (S.terminalHeadExponentEquiv t.val).property
    change S.jump (t.val.val.val+S.multiplicity-S.multiplicity) ≤ s
    simpa only [Nat.add_sub_cancel_right] using le_of_eq t.property⟩

theorem nTerminalCoordinates_monomial (t : S.TerminalExponent) :
    S.nTerminalCoordinates k (S.nonAperyMonomial k (S.terminalHeadExponentEquiv t)) = Finsupp.single t 1 := by
  rw [nTerminalCoordinates, LinearEquiv.trans_apply, S.nonAperyIdealEquiv_initial]
  simp [Finsupp.domLCongr_apply]

theorem descendingJumpMonomial_coordinates (s : ℕ) (t : S.JumpExponent s) :
    S.descendingStratumCoordinates k s (Submodule.Quotient.mk (S.descendingJumpMonomial k s t)) =
      Finsupp.single t 1 := by
  rw [S.descendingStratumCoordinates_mk]
  change Finsupp.subtypeDomain _ (S.xKernelEquiv k (S.terminalMonomial k t.val)) = _
  rw [S.xKernelEquiv_terminal]
  ext u
  change Finsupp.single t.val (1:k) u.val = Finsupp.single t (1:k) u
  by_cases h : t=u
  · subst u; simp
  · have hv : t.val ≠ u.val := fun he => h (Subtype.ext he)
    calc
      Finsupp.single t.val (1:k) u.val = 0 := Finsupp.single_eq_of_ne (Ne.symm hv)
      _ = Finsupp.single t (1:k) u := (Finsupp.single_eq_of_ne (Ne.symm h)).symm

theorem ascendingJumpMonomial_coordinates (s : ℕ) (hs : 0<s) (t : S.JumpExponent s) :
    S.ascendingStratumCoordinates k s hs (Submodule.Quotient.mk (S.ascendingJumpMonomial k s t)) =
      Finsupp.single t 1 := by
  rw [S.ascendingStratumCoordinates_mk]
  change Finsupp.subtypeDomain _
    (S.nTerminalCoordinates k (S.nonAperyMonomial k (S.terminalHeadExponentEquiv t.val))) = _
  rw [S.nTerminalCoordinates_monomial]
  ext u
  change Finsupp.single t.val (1:k) u.val = Finsupp.single t (1:k) u
  by_cases h : t=u
  · subst u; simp
  · have hv : t.val ≠ u.val := fun he => h (Subtype.ext he)
    calc
      Finsupp.single t.val (1:k) u.val = 0 := Finsupp.single_eq_of_ne (Ne.symm hv)
      _ = Finsupp.single t (1:k) u := (Finsupp.single_eq_of_ne (Ne.symm h)).symm

noncomputable def descendingStratumAction (s : ℕ) (p : S.PolynomialRing k) :
    S.DescendingJumpStratum k s →ₗ[k] S.DescendingJumpStratum k s where
  toFun a := p • a
  map_add' _ _ := smul_add _ _ _
  map_smul' c a := smul_comm p c a

noncomputable def ascendingStratumAction (s : ℕ) (p : S.PolynomialRing k) :
    S.AscendingJumpStratum k s →ₗ[k] S.AscendingJumpStratum k s where
  toFun a := p • a
  map_add' _ _ := smul_add _ _ _
  map_smul' c a := smul_comm p c a

/-- Both actual quotient actions have the same matrix in the same-jump basis. -/
theorem jump_stratum_coordinate_action (s : ℕ) (hs : 0<s) (p : S.PolynomialRing k)
    (f : S.JumpExponent s →₀ k) :
    S.descendingStratumCoordinates k s (p • (S.descendingStratumCoordinates k s).symm f) =
      S.ascendingStratumCoordinates k s hs (p • (S.ascendingStratumCoordinates k s hs).symm f) := by
  let l := (S.descendingStratumCoordinates k s).toLinearMap.comp
    ((S.descendingStratumAction k s p).comp (S.descendingStratumCoordinates k s).symm.toLinearMap)
  let q := (S.ascendingStratumCoordinates k s hs).toLinearMap.comp
    ((S.ascendingStratumAction k s p).comp (S.ascendingStratumCoordinates k s hs).symm.toLinearMap)
  have he : l=q := by
    apply Finsupp.basisSingleOne.ext
    intro t
    change S.descendingStratumCoordinates k s (p • (S.descendingStratumCoordinates k s).symm (Finsupp.single t 1)) =
      S.ascendingStratumCoordinates k s hs (p • (S.ascendingStratumCoordinates k s hs).symm (Finsupp.single t 1))
    have hd : (S.descendingStratumCoordinates k s).symm (Finsupp.single t 1) =
        Submodule.Quotient.mk (S.descendingJumpMonomial k s t) := by
      apply (S.descendingStratumCoordinates k s).injective
      rw [LinearEquiv.apply_symm_apply,S.descendingJumpMonomial_coordinates]
    have hn : (S.ascendingStratumCoordinates k s hs).symm (Finsupp.single t 1) =
        Submodule.Quotient.mk (S.ascendingJumpMonomial k s t) := by
      apply (S.ascendingStratumCoordinates k s hs).injective
      rw [LinearEquiv.apply_symm_apply,S.ascendingJumpMonomial_coordinates]
    rw [hd,hn]
    change S.descendingStratumCoordinates k s (Submodule.Quotient.mk (p • S.descendingJumpMonomial k s t)) =
      S.ascendingStratumCoordinates k s hs (Submodule.Quotient.mk (p • S.ascendingJumpMonomial k s t))
    rw [S.descendingStratumCoordinates_mk,S.ascendingStratumCoordinates_mk]
    ext u
    change S.xKernelEquiv k (p • S.terminalMonomial k t.val) u.val =
      S.nTerminalCoordinates k (p • S.nonAperyMonomial k (S.terminalHeadExponentEquiv t.val)) u.val
    rw [S.nTerminalCoordinates_apply]
    change S.tangentCoordinates k (S.polynomialToG k p*S.initialMonomial k t.val.val) u.val.val =
      S.headQuotientEquiv k (S.polynomialToA k p*S.headMonomial k (S.shiftExponent t.val.val))
        (S.terminalHeadExponentEquiv u.val).val
    exact S.same_jump_action_coordinate k (S.polynomialToG k p) t.val u.val (t.property.trans u.property.symm)
  exact LinearMap.congr_fun he f

/-- Actual S₀-module equivalence. The unrestricted T≅N vector equivalence is not used as a module map. -/
noncomputable def jumpStratumEquiv (s : ℕ) (hs : 0<s) :
    S.DescendingJumpStratum k s ≃ₗ[S.PolynomialRing k] S.AscendingJumpStratum k s where
  toEquiv := (S.jumpStratumVectorEquiv k s hs).toEquiv
  map_add' := (S.jumpStratumVectorEquiv k s hs).map_add
  map_smul' p a := by
    apply (S.ascendingStratumCoordinates k s hs).injective
    change S.ascendingStratumCoordinates k s hs
      ((S.ascendingStratumCoordinates k s hs).symm (S.descendingStratumCoordinates k s (p • a))) =
      S.ascendingStratumCoordinates k s hs (p •
        (S.ascendingStratumCoordinates k s hs).symm (S.descendingStratumCoordinates k s a))
    rw [LinearEquiv.apply_symm_apply]
    simpa only [LinearEquiv.symm_apply_apply] using
      S.jump_stratum_coordinate_action k s hs p (S.descendingStratumCoordinates k s a)

theorem descendingStratumCoordinates_symm_single (s : ℕ) (t : S.JumpExponent s) :
    (S.descendingStratumCoordinates k s).symm (Finsupp.single t 1) =
      Submodule.Quotient.mk (S.descendingJumpMonomial k s t) := by
  apply (S.descendingStratumCoordinates k s).injective
  rw [LinearEquiv.apply_symm_apply,S.descendingJumpMonomial_coordinates]

theorem ascendingStratumCoordinates_symm_single (s : ℕ) (hs : 0<s) (t : S.JumpExponent s) :
    (S.ascendingStratumCoordinates k s hs).symm (Finsupp.single t 1) =
      Submodule.Quotient.mk (S.ascendingJumpMonomial k s t) := by
  apply (S.ascendingStratumCoordinates k s hs).injective
  rw [LinearEquiv.apply_symm_apply,S.ascendingJumpMonomial_coordinates]

end NSP14.NumericalSemigroup
