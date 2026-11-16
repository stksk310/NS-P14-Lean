module
public import NSP14.Homological.KoszulSlots
public import NSP14.Homological.KoszulChainDimension
public import NSP14.Homological.KoszulExactness
public import Mathlib.LinearAlgebra.Basis.Prod
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u v
variable (k σ : Type u) [Field k] (M : ModuleCat.{u} (VariableRing k σ))
  {J : Type v} (b : Module.Basis J k (coefficientModule k σ M))

/-- An actual basis of each scalar-cone Koszul chain, indexed by the real
subset recursion and the coefficient-module basis. -/
noncomputable def koszulSlotBasis : ∀ (xs : List σ) (j : ℕ),
    Module.Basis (KoszulSlot xs.length j × J) k
      (coefficientModule k σ ((koszulList k σ xs M).X j))
  | [],0 => b.reindex (Equiv.punitProd J).symm
  | [],j+1 => by
    have : Subsingleton (coefficientModule k σ ((koszulList k σ [] M).X (j+1))) :=
      (show Subsingleton ((koszulList k σ [] M).X (j+1)) from
        ModuleCat.subsingleton_of_isZero (koszul_piece_isZero_of_gt k σ [] M (j+1) (by simp)))
    have : IsEmpty (KoszulSlot ([] : List σ).length (j+1) × J) := inferInstanceAs (IsEmpty (PEmpty × J))
    exact Module.Basis.empty _
  | x::xs,0 =>
    (koszulSlotBasis xs 0).map
      (((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapIso
        (scalarConeZeroIso (VariableRing k σ) (MvPolynomial.X x) (koszulList k σ xs M))).symm.toLinearEquiv)
  | x::xs,j+1 =>
    (((koszulSlotBasis xs j).prod (koszulSlotBasis xs (j+1))).reindex
      (Equiv.sumProdDistrib (KoszulSlot xs.length j) (KoszulSlot xs.length (j+1)) J).symm).map
        (koszulChainCoefficientSuccIso k σ x xs M j).symm.toLinearEquiv
end NSP14.Homological
