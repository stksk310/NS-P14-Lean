module
public import tests.Run13Fixtures
@[expose] public section
namespace Run13Standard
open NSP14.Homological
variable (k : Type) [Field k] (m : MonomialOrder (Fin 1))
theorem square_normal_form (p : Run13Fixtures.P1 k) :
    ∃ r, r∈normalSpace m (Run13Fixtures.squareIdeal k) ∧ p-r∈Run13Fixtures.squareIdeal k :=
  normal_form_exists m _ p
theorem square_normal_unique (r : Run13Fixtures.P1 k)
    (hr : r∈normalSpace m (Run13Fixtures.squareIdeal k)) (hi : r∈Run13Fixtures.squareIdeal k) : r=0 :=
  normal_in_ideal_eq_zero m _ r hr hi
noncomputable def square_basis := standardMonomialBasis m (Run13Fixtures.squareIdeal k)
theorem char_two_unit_minor (B : Matrix (Fin 2) (Fin 2) ℤ) (hB : B.det=1 ∨ B.det = -1) :
    (B.map (Int.castRingHom (ZMod 2))).det≠0 := signed_unit_determinant_ne_zero (ZMod 2) B hB
end Run13Standard
