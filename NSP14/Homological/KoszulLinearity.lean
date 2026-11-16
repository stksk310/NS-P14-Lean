module
public import NSP14.Homological.ScalarConeMaps
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u w
variable (R : Type u) [CommRing R]

noncomputable instance scalarConeFunctor_linear (r : R) : (scalarConeFunctor.{u,w} R r).Linear R where
  map_smul {K L} f c := by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | zero =>
      apply homotopyCofiber.ext_from_X' (r • 𝟙 K) 0 (by intro h;change _+1=0 at h;omega)
      simp
    | succ i =>
      apply homotopyCofiber.ext_from_X (r • 𝟙 K) i (i+1) (natDownStep i) <;>
        simp

noncomputable instance singleZeroFunctor_linear :
    (ChainComplex.single₀ (ModuleCat.{w} R)).Linear R where
  map_smul {M N} f c := by
    apply HomologicalComplex.Hom.ext
    funext i
    cases i with
    | zero => simp only [smul_f_apply,ChainComplex.single₀_map_f_zero]
    | succ i =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 M (i+1) (by omega)).eq_of_src _ _

variable (k σ : Type u) [Field k]

noncomputable instance koszulFunctor_linear (xs : List σ) :
    (koszulFunctor k σ xs).Linear (VariableRing k σ) := by
  induction xs with
  | nil => exact inferInstanceAs ((ChainComplex.single₀ _).Linear (VariableRing k σ))
  | cons x xs ih =>
    change (koszulFunctor k σ xs ⋙ scalarConeFunctor (VariableRing k σ) (MvPolynomial.X x)).Linear (VariableRing k σ)
    infer_instance

theorem koszulMap_scalar (xs : List σ) (M : ModuleCat.{u} (VariableRing k σ)) (r : VariableRing k σ) :
    koszulMap k σ xs (r • 𝟙 M)=r • 𝟙 (koszulList k σ xs M) := by
  change (koszulFunctor k σ xs).map (r • 𝟙 M)=_
  rw [(koszulFunctor k σ xs).map_smul,(koszulFunctor k σ xs).map_id]
  rfl
end NSP14.Homological
