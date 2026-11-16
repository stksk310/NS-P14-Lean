module

public import NSP14.Homological.Presentation
public import Mathlib.Algebra.Homology.HomotopyCofiber
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace NSP14.Homological

universe u v w

variable (k : Type u) (σ : Type v) [CommRing k]

/-- Koszul construction by the concrete subset recursion:
K(x::xs)_i = K(xs)_(i-1) ⊕ K(xs)_i, with d=(-d_old, x+d_old).
The cofiber supplies the signed block differential, not an assumed square-zero map. -/
noncomputable def koszulList (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    ChainComplex (ModuleCat.{w} (VariableRing k σ)) ℕ :=
  match xs with
  | [] => (ChainComplex.single₀ (ModuleCat (VariableRing k σ))).obj M
  | x::xs => HomologicalComplex.homotopyCofiber
      ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList xs M))

theorem koszulList_nil (M : ModuleCat.{w} (VariableRing k σ)) :
    koszulList k σ [] M = (ChainComplex.single₀ (ModuleCat (VariableRing k σ))).obj M := rfl

theorem koszulList_cons (x : σ) (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) :
    koszulList k σ (x::xs) M = HomologicalComplex.homotopyCofiber
      ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) := rfl

/-- The actual variable differential squares to zero, in every characteristic. -/
theorem koszul_d_squared (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) (i j l : ℕ) :
    (koszulList k σ xs M).d i j ≫ (koszulList k σ xs M).d j l = 0 :=
  (koszulList k σ xs M).d_comp_d i j l

/-- Abstract homology of the concrete variable complex; no Tor renaming is involved. -/
@[implicit_reducible]
noncomputable def koszulHomology (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ)) (i : ℕ) :
    ModuleCat.{w} (VariableRing k σ) := (koszulList k σ xs M).homology i

/-- The recursive chain group is a sum of the two concrete lower-rank chain groups. -/
noncomputable def koszulConsPieceIso (x : σ) (xs : List σ)
    (M : ModuleCat.{w} (VariableRing k σ)) (i : ℕ) :
    (koszulList k σ (x::xs) M).X (i+1) ≅
      (koszulList k σ xs M).X i ⊞ (koszulList k σ xs M).X (i+1) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod
    ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) (i+1) i rfl

/-- No chain group exists above the number of variables; no finrank inference is used. -/
theorem koszul_piece_isZero_of_gt (xs : List σ) (M : ModuleCat.{w} (VariableRing k σ))
    (i : ℕ) (hi : xs.length < i) : IsZero ((koszulList k σ xs M).X i) := by
  induction xs generalizing i with
  | nil =>
    exact HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 M i (by simpa using Nat.ne_zero_of_lt hi)
  | cons x xs ih =>
    apply HomologicalComplex.homotopyCofiber.isZero_X
      ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) i
    · exact ih i (by simp only [List.length_cons] at hi; omega)
    · intro j hj
      have he : j+1=i := hj
      exact ih j (by simp only [List.length_cons] at hi; omega)

end NSP14.Homological
