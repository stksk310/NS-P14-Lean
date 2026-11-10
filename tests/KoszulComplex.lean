module
public import tests.Run13Fixtures
@[expose] public section
namespace Run13Complex
open NSP14.Homological CategoryTheory
variable (k : Type) [Field k]
omit [Field k] in
theorem empty_list : variableList k (Fin 0)=[] := by
  apply List.eq_nil_of_length_eq_zero
  rw [variableList_length,Fintype.card_fin]
theorem two_variables_d_squared (M : ModuleCat (VariableRing k (Fin 2))) :
    (koszulList k (Fin 2) [0,1] M).d 2 1 ≫ (koszulList k (Fin 2) [0,1] M).d 1 0=0 :=
  koszul_d_squared k (Fin 2) [0,1] M 2 1 0
theorem top_vanishes (M : ModuleCat (VariableRing k (Fin 2))) :
    CategoryTheory.Limits.IsZero (koszulHomology k (Fin 2) [0,1] M 3) :=
  koszul_homology_isZero_of_gt k (Fin 2) [0,1] M 3 (by decide)
theorem polynomial_regular : ∀ i, (koszulList k (Fin 2) [0,1]
    (ModuleCat.of (VariableRing k (Fin 2)) (VariableRing k (Fin 2)))).ExactAt (i+1) :=
  koszul_polynomial_exact_positive k (Fin 2) [0,1] (by decide)
theorem square_homology_finite (i : ℕ) :
    Module.Finite k (koszulHomologyK k (Fin 1) (Run13Fixtures.squareModule k) i) :=
  koszul_homology_finite k (Fin 1) _ i
theorem free_betti_zero : totalBetti k (Fin 2)
    (ModuleCat.of (VariableRing k (Fin 2)) (VariableRing k (Fin 2))) 0=1 := totalBetti_free_zero k (Fin 2)
theorem free_betti_succ (i : ℕ) : totalBetti k (Fin 2)
    (ModuleCat.of (VariableRing k (Fin 2)) (VariableRing k (Fin 2))) (i+1)=0 := totalBetti_free_succ k (Fin 2) i
end Run13Complex
