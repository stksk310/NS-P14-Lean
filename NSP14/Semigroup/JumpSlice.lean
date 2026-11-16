module

public import NSP14.Semigroup.JumpFiltration

@[expose] public section

open scoped Classical

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

noncomputable def nTerminalCoordinates :
    (S.nonAperyIdeal k).restrictScalars k ≃ₗ[k] (S.TerminalExponent →₀ k) :=
  (S.nonAperyIdealEquiv k).trans (Finsupp.domLCongr S.terminalHeadExponentEquiv.symm)

theorem nTerminalCoordinates_apply (a : (S.nonAperyIdeal k).restrictScalars k) (t : S.TerminalExponent) :
    S.nTerminalCoordinates k a t = S.headQuotientEquiv k a.val (S.terminalHeadExponentEquiv t).val := by
  simp only [nTerminalCoordinates, LinearEquiv.trans_apply, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply]
  rfl

theorem mem_descendingJump_coordinates (s : ℕ) (a : (S.xMultiply k).ker) :
    a ∈ S.descendingJump k s ↔
      ∀ t : S.TerminalExponent, S.jump t.val.val < s → S.xKernelEquiv k a t = 0 := by
  rw [S.mem_descendingJump]
  constructor
  · intro h t ht
    exact h t.val (by rintro ⟨_,hh⟩; omega)
  · intro h t ht
    by_cases hterm : S.Terminal t.val
    · exact h ⟨t,hterm⟩ (show S.jump t.val < s by by_contra hh; exact ht ⟨hterm,by omega⟩)
    · have ha := (S.mem_xKernel_coordinates k a.val).1 a.property
      rw [S.coordinateShift_ker] at ha
      exact (Finsupp.mem_supported' k _).1 ha t hterm

theorem mem_ascendingJump_coordinates (s : ℕ) (a : (S.nonAperyIdeal k).restrictScalars k) :
    a ∈ S.ascendingJump k s ↔
      ∀ t : S.TerminalExponent, s < S.jump t.val.val → S.nTerminalCoordinates k a t = 0 := by
  rw [S.mem_ascendingJump]
  constructor
  · intro h t ht
    rw [S.nTerminalCoordinates_apply]
    apply h
    intro hh
    have hh := hh.2
    change S.jump (t.val.val+S.multiplicity-S.multiplicity) ≤ s at hh
    simp only [Nat.add_sub_cancel_right] at hh
    omega
  · intro h y hy
    by_cases hn : y.val.val ∉ S.aperySet
    · let z : S.NonAperyHeadExponent := ⟨y,hn⟩
      let t := S.terminalHeadExponentEquiv.symm z
      have hz : S.terminalHeadExponentEquiv t = z := Equiv.apply_symm_apply _ z
      have hne : s < S.jump t.val.val := by
        change s < S.jump (y.val.val-S.multiplicity)
        by_contra hh
        exact hy ⟨hn,by omega⟩
      have he := h t hne
      rw [S.nTerminalCoordinates_apply, hz] at he
      exact he
    · exact (S.mem_nonAperySpace k a.val).1 a.property y (not_not.mp hn)

noncomputable instance descendingJumpAddCommGroup (s : ℕ) : AddCommGroup (S.descendingJump k s) :=
  (S.descendingJump k s).addCommGroup

noncomputable instance ascendingJumpAddCommGroup (s : ℕ) : AddCommGroup (S.ascendingJump k s) :=
  (S.ascendingJump k s).addCommGroup

noncomputable instance descendingJumpModule (s : ℕ) : Module (S.PolynomialRing k) (S.descendingJump k s) :=
  (S.descendingJump k s).module

noncomputable instance ascendingJumpModule (s : ℕ) : Module (S.PolynomialRing k) (S.ascendingJump k s) :=
  (S.ascendingJump k s).module

noncomputable def nextDescendingJump (s : ℕ) : Submodule (S.PolynomialRing k) (S.descendingJump k s) :=
  (S.descendingJump k (s+1)).comap (S.descendingJump k s).subtype

noncomputable def previousAscendingJump (s : ℕ) : Submodule (S.PolynomialRing k) (S.ascendingJump k s) :=
  (S.ascendingJump k (s-1)).comap (S.ascendingJump k s).subtype

abbrev DescendingJumpStratum (s : ℕ) := (S.descendingJump k s) ⧸ (S.nextDescendingJump k s)
abbrev AscendingJumpStratum (s : ℕ) := (S.ascendingJump k s) ⧸ (S.previousAscendingJump k s)

def JumpExponent (s : ℕ) := {t : S.TerminalExponent // S.jump t.val.val = s}

noncomputable def descendingSlice (s : ℕ) : (S.descendingJump k s) →ₗ[k] (S.JumpExponent s →₀ k) :=
  (Finsupp.lsubtypeDomain {t : S.TerminalExponent | S.jump t.val.val = s}).comp
    ((S.xKernelEquiv k).toLinearMap.comp ((S.descendingJump k s).restrictScalars k).subtype)

noncomputable def ascendingSlice (s : ℕ) : (S.ascendingJump k s) →ₗ[k] (S.JumpExponent s →₀ k) :=
  (Finsupp.lsubtypeDomain {t : S.TerminalExponent | S.jump t.val.val = s}).comp
    ((S.nTerminalCoordinates k).toLinearMap.comp ((S.ascendingJump k s).restrictScalars k).subtype)

theorem descendingSlice_ker (s : ℕ) : (S.descendingSlice k s).ker = (S.nextDescendingJump k s).restrictScalars k := by
  ext a
  change Finsupp.subtypeDomain _ (S.xKernelEquiv k a.val) = 0 ↔ a.val ∈ S.descendingJump k (s+1)
  rw [Finsupp.subtypeDomain_eq_zero_iff', S.mem_descendingJump_coordinates]
  constructor
  · intro h t ht
    by_cases he : S.jump t.val.val=s
    · exact h t he
    · exact (S.mem_descendingJump_coordinates k s a.val).1 a.property t (by omega)
  · intro h t ht
    change S.jump t.val.val = s at ht
    exact h t (by omega)

theorem ascendingSlice_ker (s : ℕ) (hs : 0 < s) :
    (S.ascendingSlice k s).ker = (S.previousAscendingJump k s).restrictScalars k := by
  ext a
  change Finsupp.subtypeDomain _ (S.nTerminalCoordinates k a.val) = 0 ↔ a.val ∈ S.ascendingJump k (s-1)
  rw [Finsupp.subtypeDomain_eq_zero_iff', S.mem_ascendingJump_coordinates]
  constructor
  · intro h t ht
    by_cases he : S.jump t.val.val=s
    · exact h t he
    · exact (S.mem_ascendingJump_coordinates k s a.val).1 a.property t (by omega)
  · intro h t ht
    change S.jump t.val.val = s at ht
    exact h t (by omega)

theorem descendingSlice_surjective (s : ℕ) : Function.Surjective (S.descendingSlice k s) := by
  intro f
  let a := (S.xKernelEquiv k).symm f.extendDomain
  have ha : a ∈ S.descendingJump k s := by
    rw [S.mem_descendingJump_coordinates]
    intro t ht
    change S.xKernelEquiv k ((S.xKernelEquiv k).symm f.extendDomain) t=0
    rw [LinearEquiv.apply_symm_apply]
    apply (Finsupp.mem_supported' k _).1 f.support_extendDomain_subset
    change S.jump t.val.val ≠ s
    omega
  refine ⟨⟨a,ha⟩, ?_⟩
  change Finsupp.subtypeDomain _ (S.xKernelEquiv k a) = f
  rw [show S.xKernelEquiv k a = f.extendDomain from LinearEquiv.apply_symm_apply _ _]
  exact Finsupp.subtypeDomain_extendDomain f

theorem ascendingSlice_surjective (s : ℕ) : Function.Surjective (S.ascendingSlice k s) := by
  intro f
  let a := (S.nTerminalCoordinates k).symm f.extendDomain
  have ha : a ∈ S.ascendingJump k s := by
    rw [S.mem_ascendingJump_coordinates]
    intro t ht
    change S.nTerminalCoordinates k ((S.nTerminalCoordinates k).symm f.extendDomain) t=0
    rw [LinearEquiv.apply_symm_apply]
    apply (Finsupp.mem_supported' k _).1 f.support_extendDomain_subset
    change S.jump t.val.val ≠ s
    omega
  refine ⟨⟨a,ha⟩, ?_⟩
  change Finsupp.subtypeDomain _ (S.nTerminalCoordinates k a) = f
  rw [show S.nTerminalCoordinates k a = f.extendDomain from LinearEquiv.apply_symm_apply _ _]
  exact Finsupp.subtypeDomain_extendDomain f

/-- Coordinates of the actual descending S₀-module quotient, viewed over k. -/
noncomputable def descendingStratumCoordinates (s : ℕ) :
    S.DescendingJumpStratum k s ≃ₗ[k] (S.JumpExponent s →₀ k) :=
  (Submodule.quotEquivOfEq _ _ (S.descendingSlice_ker k s).symm).trans
    ((S.descendingSlice k s).quotKerEquivOfSurjective (S.descendingSlice_surjective k s))

/-- Coordinates of the actual ascending S₀-module quotient, viewed over k. -/
noncomputable def ascendingStratumCoordinates (s : ℕ) (hs : 0 < s) :
    S.AscendingJumpStratum k s ≃ₗ[k] (S.JumpExponent s →₀ k) :=
  (Submodule.quotEquivOfEq _ _ (S.ascendingSlice_ker k s hs).symm).trans
    ((S.ascendingSlice k s).quotKerEquivOfSurjective (S.ascendingSlice_surjective k s))

noncomputable def jumpStratumVectorEquiv (s : ℕ) (hs : 0 < s) :
    S.DescendingJumpStratum k s ≃ₗ[k] S.AscendingJumpStratum k s :=
  (S.descendingStratumCoordinates k s).trans (S.ascendingStratumCoordinates k s hs).symm

theorem descendingStratumCoordinates_mk (s : ℕ) (a : S.descendingJump k s) :
    S.descendingStratumCoordinates k s (Submodule.Quotient.mk a) = S.descendingSlice k s a := rfl

theorem ascendingStratumCoordinates_mk (s : ℕ) (hs : 0 < s) (a : S.ascendingJump k s) :
    S.ascendingStratumCoordinates k s hs (Submodule.Quotient.mk a) = S.ascendingSlice k s a := rfl

end NSP14.NumericalSemigroup
