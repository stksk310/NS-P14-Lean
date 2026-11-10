module
import NSP14
import tests.Run12Fixtures
import Mathlib.Data.ZMod.Basic

open NSP14
open scoped Classical BigOperators
noncomputable section
namespace NSP14.Run12StrataAudit

-- An independent uniform-jump example: actual <5,6,13>.
private def allowed : Finset ℕ := {0,5,6,10,11,12,13,15,16,17,18,19}
private def S : NumericalSemigroup where
  carrier :=
    { carrier := {n | n∈allowed ∨ 20≤n}
      zero_mem' := Or.inl (by decide)
      add_mem' := by
        intro x y hx hy
        change x+y∈allowed ∨ 20≤x+y
        change x∈allowed ∨ 20≤x at hx
        change y∈allowed ∨ 20≤y at hy
        simp only [allowed,Finset.mem_insert,Finset.mem_singleton] at hx hy ⊢
        omega }
  conductor := 20
  cofinite _ h := Or.inr h
private theorem m_five : S.multiplicity=5 := by
  apply S.multiplicity_eq (by decide) (show 5∈S from Or.inl (by decide))
  intro x hx hp
  change x∈allowed ∨ 20≤x at hx
  simp only [allowed,Finset.mem_insert,Finset.mem_singleton] at hx
  omega
private def v6 : S.carrier := ⟨6,Or.inl (by decide)⟩
private def v13 : S.carrier := ⟨13,Or.inl (by decide)⟩
private def v18 : S.carrier := ⟨18,Or.inl (by decide)⟩
private def v19 : S.carrier := ⟨19,Or.inl (by decide)⟩
private def v24 : S.carrier := ⟨24,Or.inr (by decide)⟩
private def weight (n : ℕ) : ℕ :=
  [0,0,0,0,0,1,1,0,0,0,2,2,2,1,0,3,3,3,3,2,4,4,4,4,4][n]?.getD 0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem weight_step : ∀ x∈Finset.range 25, ∀ y∈Finset.range 25,
    (x∈allowed ∨ 20≤x) → 0<x → (y∈allowed ∨ 20≤y) → x+y≤24 →
      weight y+1≤weight (x+y) := by decide
private theorem order_le (x : S.carrier) (hx : x.val≤24) : S.order x.val≤weight x.val := by
  apply Run12Fixtures.length_weight_bound S 24 weight ?_ (S.order_length x.property) hx
  intro a ha hp b hb hab
  exact weight_step a (Finset.mem_range.mpr (by omega)) b
    (Finset.mem_range.mpr (by omega)) ha hp hb hab
private theorem ord6 : S.order 6=1 := by
  have hl := S.order_pos v6.property (by decide : 0<6)
  have hh := order_le v6 (by decide)
  change S.order 6≤weight 6 at hh
  change 0<S.order 6 at hl
  norm_num [weight] at hh
  omega
private theorem ord13 : S.order 13=1 := by
  have hl := S.order_pos v13.property (by decide : 0<13)
  have hh := order_le v13 (by decide)
  change S.order 13≤weight 13 at hh
  change 0<S.order 13 at hl
  norm_num [weight] at hh
  omega
private theorem ord18 : S.order 18=3 := by
  have hl := S.length_le_order (show S.HasLength 18 3 from
    ⟨fun _ => 6,fun _ => ⟨v6.property,by norm_num⟩,by norm_num⟩)
  have hh := order_le v18 (by decide)
  change S.order 18≤weight 18 at hh
  norm_num [weight] at hh
  omega
private theorem ord19 : S.order 19=2 := by
  have hl := S.order_add v13.property v6.property
  change S.order 13+S.order 6≤S.order 19 at hl
  rw [ord13,ord6] at hl
  have hh := order_le v19 (by decide)
  change S.order 19≤weight 19 at hh
  norm_num [weight] at hh
  omega
private theorem ord24 : S.order 24=4 := by
  have hl := S.length_le_order (show S.HasLength 24 4 from
    ⟨fun _ => 6,fun _ => ⟨v6.property,by norm_num⟩,by norm_num⟩)
  have hh := order_le v24 (by decide)
  change S.order 24≤weight 24 at hh
  norm_num [weight] at hh
  omega
private theorem terminal13 : S.Terminal 13 := by
  refine ⟨v13.property,?_⟩
  rw [m_five,ord13]
  change 2<S.order 18
  rw [ord18]; decide
private theorem terminal19 : S.Terminal 19 := by
  refine ⟨v19.property,?_⟩
  rw [m_five,ord19]
  change 3<S.order 24
  rw [ord24]; decide
private def j13 : S.JumpExponent 2 := ⟨⟨v13,terminal13⟩,by
  change S.order (13+S.multiplicity)-S.order 13=2
  rw [m_five,ord13]
  change S.order 18-1=2
  rw [ord18]⟩
private def j19 : S.JumpExponent 2 := ⟨⟨v19,terminal19⟩,by
  change S.order (19+S.multiplicity)-S.order 19=2
  rw [m_five,ord19]
  change S.order 24-2=2
  rw [ord24]⟩
private def atom6 : S.NonXAtom := ⟨v6,(S.order_one_iff_atom v6.property).1 ord6,by rw [m_five]; decide⟩

private def dclass (k : Type*) [CommRing k] [Nontrivial k] (j : S.JumpExponent 2) :
    S.DescendingJumpStratum k 2 := Submodule.Quotient.mk (S.descendingJumpMonomial k 2 j)

-- A real nonzero polynomial action survives inside one jump stratum.
private theorem live_action (k : Type*) [CommRing k] [Nontrivial k] :
    (MvPolynomial.X atom6 : S.PolynomialRing k) • dclass k j13=dclass k j19 := by
  change (Submodule.Quotient.mk ((MvPolynomial.X atom6 : S.PolynomialRing k) •
    S.descendingJumpMonomial k 2 j13) : S.DescendingJumpStratum k 2)=_
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  change S.polynomialToG k (MvPolynomial.X atom6)*S.initialMonomial k v13=S.initialMonomial k v19
  rw [S.polynomialToG_X]
  apply S.initialMonomial_mul_live
  change S.order 19=S.order 6+S.order 13
  rw [ord19,ord6,ord13]

example (k : Type*) [CommRing k] [Nontrivial k] :
    (MvPolynomial.X atom6 : S.PolynomialRing k) • dclass k j13≠0 := by
  rw [live_action]
  intro hz
  have he := congrArg (S.descendingStratumCoordinates k 2) hz
  change S.descendingStratumCoordinates k 2 (Submodule.Quotient.mk _)=_ at he
  rw [S.descendingJumpMonomial_coordinates,map_zero] at he
  exact Finsupp.single_ne_zero.mpr one_ne_zero he

example (k : Type*) [CommRing k] [Nontrivial k] :
    (MvPolynomial.X atom6 : S.PolynomialRing k) • S.jumpStratumEquiv k 2 (by decide) (dclass k j13) =
      S.jumpStratumEquiv k 2 (by decide) (dclass k j19) := by
  rw [← map_smul,live_action]

example (k : Type*) [CommRing k] [Nontrivial k] :
    (MvPolynomial.X atom6 : S.PolynomialRing k) • S.jumpStratumEquiv k 2 (by decide) (dclass k j13)≠0 := by
  rw [← map_smul]
  intro hz
  have hn := (S.jumpStratumEquiv k 2 (by decide)).injective (hz.trans (map_zero _).symm)
  rw [live_action] at hn
  have he := congrArg (S.descendingStratumCoordinates k 2) hn
  change S.descendingStratumCoordinates k 2 (Submodule.Quotient.mk _)=_ at he
  rw [S.descendingJumpMonomial_coordinates,map_zero] at he
  exact Finsupp.single_ne_zero.mpr one_ne_zero he



-- The comparison preserves actual kernel elements and actual x multiplication.
example (k : Type*) [CommRing k] [Nontrivial k] :
    S.formalInitialMonomial k v13≠0 := by
  rw [← S.completedGradedAlgEquiv_initial]
  intro hz
  apply S.initialMonomial_ne_zero k v13
  exact (S.completedGradedAlgEquiv k).injective (hz.trans (map_zero _).symm)
example (k : Type*) [CommRing k] [Nontrivial k] :
    S.formalXMultiply k (S.formalInitialMonomial k v13)=0 := by
  rw [← S.completedGradedAlgEquiv_initial,← S.completedGradedAlgEquiv_xMultiply]
  rw [S.xMultiply_initial_dead k v13 ((S.not_live_iff_terminal v13).2 terminal13),map_zero]

#print axioms live_action
#print axioms terminal19
end NSP14.Run12StrataAudit
