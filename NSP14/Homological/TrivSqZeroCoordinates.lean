module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
@[expose] public section
namespace NSP14.Homological
universe u
variable (k σ τ : Type u) [Field k] (e : (σ → k) ≃ₗ[k] (τ → k))

noncomputable def trivSqZeroCoordinatesLinearEquiv :
    TrivSqZeroExt k (σ → k) ≃ₗ[k] TrivSqZeroExt k (τ → k) :=
  LinearEquiv.prodCongr (LinearEquiv.refl k k) e

theorem trivSqZeroCoordinates_one : trivSqZeroCoordinatesLinearEquiv k σ τ e 1=1 := by
  apply TrivSqZeroExt.ext
  · rfl
  · exact map_zero e

theorem trivSqZeroCoordinates_mul (a b : TrivSqZeroExt k (σ → k)) :
    trivSqZeroCoordinatesLinearEquiv k σ τ e (a*b)=
      trivSqZeroCoordinatesLinearEquiv k σ τ e a*trivSqZeroCoordinatesLinearEquiv k σ τ e b := by
  apply TrivSqZeroExt.ext
  · rfl
  · change e (a*b).snd=_
    rw [TrivSqZeroExt.snd_mul,TrivSqZeroExt.snd_mul,op_smul_eq_smul,op_smul_eq_smul,map_add,map_smul,map_smul]
    rfl

noncomputable def trivSqZeroCoordinatesEquiv :
    TrivSqZeroExt k (σ → k) ≃ₐ[k] TrivSqZeroExt k (τ → k) :=
  AlgEquiv.ofLinearEquiv (trivSqZeroCoordinatesLinearEquiv k σ τ e)
    (trivSqZeroCoordinates_one k σ τ e) (trivSqZeroCoordinates_mul k σ τ e)
end NSP14.Homological
