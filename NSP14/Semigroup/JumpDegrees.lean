module

public import NSP14.Semigroup.JumpStrata
public import NSP14.Semigroup.CoordinateSupport

@[expose] public section

open scoped Classical BigOperators

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type*) [CommRing k] [Nontrivial k]

/-- The actual degree-p image in the algebraic associated graded. -/
noncomputable def tangentDegree (p : ℕ) : Submodule k (S.TangentAlgebra k) :=
  (DirectSum.lof k ℕ (S.GradedPiece k) p).range

omit [Nontrivial k] in
theorem initialMonomial_mem_tangentDegree (p : ℕ) (t : S.carrier) (ht : S.order t.val=p) :
    S.initialMonomial k t ∈ S.tangentDegree k p := by
  subst p
  exact ⟨S.monomialClass k _ t le_rfl,rfl⟩

omit [Nontrivial k] in
theorem mem_tangentDegree_coordinates (p : ℕ) (a : S.TangentAlgebra k) :
    a ∈ S.tangentDegree k p ↔ S.tangentCoordinates k a ∈
      Finsupp.supported k k {t : S.carrier | S.order t.val=p} := by
  constructor
  · rintro ⟨b,rfl⟩
    rw [Finsupp.mem_supported']
    intro t ht
    exact S.tangentCoordinates_of_ne k p b t ht
  · intro ha
    have hs := (Finsupp.mem_supported k _).1 ha
    rw [← S.tangent_expansion k a,Finsupp.sum]
    apply (S.tangentDegree k p).sum_mem
    intro t ht
    exact (S.tangentDegree k p).smul_mem _ (S.initialMonomial_mem_tangentDegree k p t (hs ht))

/-- Homogeneous representatives in the actual descending filtration. -/
noncomputable def descendingHomogeneous (s p : ℕ) : Submodule k (S.descendingJump k s) :=
  (S.tangentDegree k p).comap
    ((S.xMultiply k).ker.subtype.comp ((S.descendingJump k s).restrictScalars k).subtype)

/-- Homogeneous representatives in N use A's inherited grading. -/
noncomputable def ascendingHomogeneous (s q : ℕ) : Submodule k (S.ascendingJump k s) :=
  (S.headDegree k q).comap
    (((S.nonAperyIdeal k).restrictScalars k).subtype.comp ((S.ascendingJump k s).restrictScalars k).subtype)

/-- Degrees are quotient images of actual homogeneous representatives, not freely assigned labels. -/
noncomputable def descendingStratumDegree (s p : ℕ) : Submodule k (S.DescendingJumpStratum k s) :=
  (S.descendingHomogeneous k s p).map ((S.nextDescendingJump k s).restrictScalars k).mkQ

noncomputable def ascendingStratumDegree (s q : ℕ) : Submodule k (S.AscendingJumpStratum k s) :=
  (S.ascendingHomogeneous k s q).map ((S.previousAscendingJump k s).restrictScalars k).mkQ

theorem descendingStratumDegree_coordinates (s p : ℕ) : S.descendingStratumDegree k s p =
    (Finsupp.supported k k {t : S.JumpExponent s | S.order t.val.val.val=p}).comap
      (S.descendingStratumCoordinates k s).toLinearMap := by
  apply le_antisymm
  · rintro a ⟨b,hb,rfl⟩
    have hbc := (S.mem_tangentDegree_coordinates k p b.val.val).1 hb
    change S.descendingStratumCoordinates k s (Submodule.Quotient.mk b) ∈
      Finsupp.supported k k {t : S.JumpExponent s | S.order t.val.val.val=p}
    rw [S.descendingStratumCoordinates_mk,Finsupp.mem_supported']
    intro t ht
    exact (Finsupp.mem_supported' k _).1 hbc t.val.val ht
  · rw [NSP14.supported_comap_eq_span]
    apply Submodule.span_le.mpr
    rintro a ⟨t,ht,rfl⟩
    change (S.descendingStratumCoordinates k s).symm (Finsupp.single t 1) ∈ S.descendingStratumDegree k s p
    rw [S.descendingStratumCoordinates_symm_single]
    refine ⟨S.descendingJumpMonomial k s t,?_,rfl⟩
    exact S.initialMonomial_mem_tangentDegree k p t.val.val ht

theorem ascendingStratumDegree_coordinates (s q : ℕ) (hs : 0<s) : S.ascendingStratumDegree k s q =
    (Finsupp.supported k k {t : S.JumpExponent s |
      S.order (S.terminalHeadExponentEquiv t.val).val.val.val=q}).comap
        (S.ascendingStratumCoordinates k s hs).toLinearMap := by
  apply le_antisymm
  · rintro a ⟨b,hb,rfl⟩
    have hbc := (S.mem_headDegree_coordinates k q b.val.val).1 hb
    change S.ascendingStratumCoordinates k s hs (Submodule.Quotient.mk b) ∈
      Finsupp.supported k k {t : S.JumpExponent s | S.order (S.terminalHeadExponentEquiv t.val).val.val.val=q}
    rw [S.ascendingStratumCoordinates_mk,Finsupp.mem_supported']
    intro t ht
    change S.nTerminalCoordinates k b.val t.val = 0
    rw [S.nTerminalCoordinates_apply]
    exact (Finsupp.mem_supported' k _).1 hbc (S.terminalHeadExponentEquiv t.val).val ht
  · rw [NSP14.supported_comap_eq_span]
    apply Submodule.span_le.mpr
    rintro a ⟨t,ht,rfl⟩
    change (S.ascendingStratumCoordinates k s hs).symm (Finsupp.single t 1) ∈ S.ascendingStratumDegree k s q
    rw [S.ascendingStratumCoordinates_symm_single]
    refine ⟨S.ascendingJumpMonomial k s t,?_,rfl⟩
    exact S.headMonomial_mem_degree k (S.terminalHeadExponentEquiv t.val).val.val q ht

/-- The same S₀-linear equivalence shifts actual homogeneous degree by exactly s. -/
theorem jumpStratumEquiv_degree (s : ℕ) (hs : 0<s) (p : ℕ) (a : S.DescendingJumpStratum k s) :
    S.jumpStratumEquiv k s hs a ∈ S.ascendingStratumDegree k s (p+s) ↔
      a ∈ S.descendingStratumDegree k s p := by
  rw [S.ascendingStratumDegree_coordinates k s (p+s) hs,S.descendingStratumDegree_coordinates]
  have hc : S.ascendingStratumCoordinates k s hs (S.jumpStratumEquiv k s hs a) =
      S.descendingStratumCoordinates k s a := LinearEquiv.apply_symm_apply _ _
  change S.ascendingStratumCoordinates k s hs (S.jumpStratumEquiv k s hs a) ∈
    Finsupp.supported k k {t : S.JumpExponent s | S.order (S.terminalHeadExponentEquiv t.val).val.val.val=p+s} ↔
      S.descendingStratumCoordinates k s a ∈
        Finsupp.supported k k {t : S.JumpExponent s | S.order t.val.val.val=p}
  rw [hc]
  have hp : {t : S.JumpExponent s | S.order (S.terminalHeadExponentEquiv t.val).val.val.val=p+s} =
      {t : S.JumpExponent s | S.order t.val.val.val=p} := by
    ext t
    have hd := S.terminal_head_degree_shift_of_jump t.val s t.property
    change (_=p+s) ↔ (_=p)
    rw [hd]
    omega
  rw [hp]

end NSP14.NumericalSemigroup
