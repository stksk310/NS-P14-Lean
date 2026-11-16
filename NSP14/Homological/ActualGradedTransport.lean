module

public import NSP14.Homological.ActualGrading
public import NSP14.Homological.KoszulGradedMaps

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory NSP14.Homological

namespace NSP14.NumericalSemigroup

variable (S : NSP14.NumericalSemigroup) (k : Type) [Field k]

theorem jumpStratumGrading_shift (s : ℕ) (hs : 0<s) (q : ℤ)
    (a : coefficientModule k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s))) :
    (S.jumpStratumEquiv k s hs).toModuleIso.hom a∈(S.ascendingStratumGrading k s hs).degreeSpace (q+(s:ℤ)) ↔
      a∈(S.descendingStratumGrading k s).degreeSpace q := by
  change (S.jumpStratumEquiv k s hs).toModuleIso.hom a∈
    (coordinateDegreeInclusion k (S.JumpExponent s)
      (fun t => ((S.order (S.terminalHeadExponentEquiv t.val).val.val.val : ℕ) : ℤ))
      S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s))
      ((coefficientOriginalEquiv k S.NonXAtom (S.AscendingJumpStratum k s)).trans
        (S.ascendingStratumCoordinates k s hs)) (q+(s:ℤ))).range ↔
    a∈(coordinateDegreeInclusion k (S.JumpExponent s)
      (fun t => ((S.order t.val.val.val : ℕ) : ℤ)) S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s))
      ((coefficientOriginalEquiv k S.NonXAtom (S.DescendingJumpStratum k s)).trans
        (S.descendingStratumCoordinates k s)) q).range
  rw [coordinateDegreeInclusion_range,coordinateDegreeInclusion_range]
  change (∀ t,((S.order (S.terminalHeadExponentEquiv t.val).val.val.val : ℕ):ℤ)≠q+(s:ℤ) →
    S.ascendingStratumCoordinates k s hs (S.jumpStratumEquiv k s hs a) t=0) ↔
    ∀ t,((S.order t.val.val.val : ℕ):ℤ)≠q → S.descendingStratumCoordinates k s a t=0
  have hc : S.ascendingStratumCoordinates k s hs (S.jumpStratumEquiv k s hs a)=
      S.descendingStratumCoordinates k s a := LinearEquiv.apply_symm_apply _ _
  rw [hc]
  apply forall_congr'
  intro t
  have hd := S.terminal_head_degree_shift_of_jump t.val s t.property
  rw [hd,Nat.cast_add]
  simp only [ne_eq,add_left_inj]

/-- The Run12 same-jump map on the actual internally graded Koszul complexes. -/
noncomputable def jumpStratumGradedKoszulIso (s : ℕ) (hs : 0<s) (t : ℤ) :
    gradedKoszulComplex k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s)) (S.descendingStratumGrading k s) (variableList k S.NonXAtom) t ≅
      gradedKoszulComplex k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s)) (S.ascendingStratumGrading k s hs) (variableList k S.NonXAtom) (t+(s:ℤ)) :=
  gradedKoszulIso k S.NonXAtom (S.descendingStratumGrading k s) (S.ascendingStratumGrading k s hs)
    (S.jumpStratumEquiv k s hs).toModuleIso (s:ℤ) (S.jumpStratumGrading_shift k s hs)
    (variableList k S.NonXAtom) t

/-- Graded Betti keeps the exact inherited shift s, rather than identifying equal degrees. -/
theorem jumpStratum_gradedBetti (s : ℕ) (hs : 0<s) (i : ℕ) (t : ℤ) :
    gradedBetti k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.DescendingJumpStratum k s)) (S.descendingStratumGrading k s) i t =
      gradedBetti k S.NonXAtom (ModuleCat.of (S.PolynomialRing k) (S.AscendingJumpStratum k s)) (S.ascendingStratumGrading k s hs) i (t+(s:ℤ)) :=
  ((HomologicalComplex.homologyFunctor _ (ComplexShape.down ℕ) i).mapIso
    (S.jumpStratumGradedKoszulIso k s hs t)).toLinearEquiv.finrank_eq

end NSP14.NumericalSemigroup
