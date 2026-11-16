module
public import NSP14.Homological.KoszulMomentRank
public import NSP14.Homological.InfiniteScalarField
public import NSP14.ArithmeticSequence.ModelKernel
public import NSP14.ArithmeticSequence.OrdinaryModel
public import tests.ArithmeticSequenceConeBetti
@[expose] public section
open NSP14 NSP14.Homological
namespace APResolutionFoundationsAcceptance

abbrev K := InfiniteScalarField (ZMod 2)
noncomputable def points (i : Fin 3) : K := Infinite.natEmbedding K i.val

theorem points_injective : Function.Injective points := by
  intro i j h
  exact Fin.ext ((Infinite.natEmbedding K).injective h)

/-- Critical signed block after evaluation change, over a genuine
same-characteristic infinite extension of the field of two elements. -/
theorem critical_char_two : Function.Bijective (koszulMomentMap K (Fin 3) points 2 2 1) :=
  koszulMomentMap_bijective K (Fin 3) points points_injective 2 2 (by decide) (by decide)

theorem upper_injective : Function.Injective (koszulMomentMap K (Fin 3) points 2 2 2) :=
  koszulMomentMap_injective K (Fin 3) points points_injective 2 2 2 (by decide) (by decide)

theorem lower_surjective : Function.Surjective (koszulMomentMap K (Fin 3) points 2 2 0) :=
  koszulMomentMap_surjective K (Fin 3) points points_injective 2 2 0 (by decide) (by decide)

abbrev D := ArithmeticSequenceConeBettiAcceptance.mixed

theorem actual_model_order :
    (D.ordinaryModel (by decide)).source.order 14=4 := by
  rw [D.ordinaryModel_order (by decide) ((D.ordinaryModel_mem (by decide) 14).mpr (by right;decide))]
  decide

theorem actual_model_first :
    let B := (D.ordinaryModel (by decide)).source
    totalBetti (ZMod 2) B.AtomExponent
      (ModuleCat.of (B.FullPolynomialRing (ZMod 2)) (B.TangentAlgebra (ZMod 2))) 1=3 := by
  dsimp only
  rw [(D.ordinaryModel (by decide)).maximalEmbedding_betti (ZMod 2) rfl 1 (by decide)]
  decide

theorem actual_auxiliary_surjection : Function.Surjective (D.modelToHead (by decide) (ZMod 2)) :=
  D.modelToHead_surjective (by decide) (ZMod 2)

theorem actual_head_dead_product : D.headIndexMonomial (ZMod 2) 1*D.headIndexMonomial (ZMod 2) 1=0 := by
  rw [D.headIndexMonomial_mul,ite_eq_right (by decide)]

theorem actual_head_live_product : D.headIndexMonomial (ZMod 2) 2*D.headIndexMonomial (ZMod 2) 2=
    D.headIndexMonomial (ZMod 2) 4 := by
  rw [D.headIndexMonomial_mul,ite_eq_left (by decide)]

theorem actual_kernel_monomial : D.modelMonomial (by decide) (ZMod 2) 5∈D.modelKernel (by decide) (ZMod 2) :=
  (D.modelKernelMonomial (by decide) (ZMod 2) ⟨5,by decide⟩).property
end APResolutionFoundationsAcceptance
