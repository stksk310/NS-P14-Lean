module
public import NSP14.Homological.CoefficientKoszulListFunctor
@[expose] public section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k]

theorem coefficientKoszulList_homology_isZero_of_gt (xs : List σ)
    (M : ModuleCat.{u} (VariableRing k σ)) (i : ℕ) (hi : xs.length < i) :
    IsZero (((coefficientKoszulListFunctor k σ xs).obj M).homology i) := by
  have hz : IsZero (((coefficientKoszulListFunctor k σ xs).obj M).X i) :=
    (ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).map_isZero
      (koszul_piece_isZero_of_gt k σ xs M i hi)
  exact HomologicalComplex.ExactAt.isZero_homology (HomologicalComplex.ExactAt.of_isZero hz)

theorem complex_homology_isZero_of_iso {K J : ChainComplex (ModuleCat.{u} k) ℕ}
    (e : K ≅ J) (i : ℕ) (h : IsZero (J.homology i)) : IsZero (K.homology i) :=
  IsZero.of_iso h ((homologyFunctor (ModuleCat k) (ComplexShape.down ℕ) i).mapIso e)
end NSP14.Homological
