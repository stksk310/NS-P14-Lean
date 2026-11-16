module
public import NSP14.Homological.KoszulExteriorMap
public import NSP14.Homological.ExteriorContraction
@[expose] public section
open scoped Classical
namespace NSP14.Tests.KoszulExteriorMap
open Homological
theorem actual_change_contraction (k σ : Type) [Field k] [Fintype σ] (j : ℕ)
    (e : (σ → k) ≃ₗ[k] (σ → k)) (φ : Module.Dual k (σ → k))
    (w : ⋀[k]^(j+1) (σ → k)) :
    koszulExteriorContraction k σ j φ (exteriorPowerLinearEquiv k (j+1) e w)=
      exteriorPowerLinearEquiv k j e (koszulExteriorContraction k σ j (φ.comp e.toLinearMap) w) :=
  koszulExteriorContraction_naturality k σ j e φ w

theorem actual_removed_coordinate_stability (k σ : Type) [Field k] [Fintype σ] (j : ℕ)
    (f g : (σ → k) →ₗ[k] (σ → k)) (x : σ)
    (hfg : ∀ y, y≠x → f (Pi.single y 1)=g (Pi.single y 1))
    (w : ⋀[k]^(j+1) (σ → k)) :
    exteriorPower.map j f (koszulExteriorContraction k σ j (LinearMap.proj x) w)=
      exteriorPower.map j g (koszulExteriorContraction k σ j (LinearMap.proj x) w) :=
  koszulExteriorMap_coordinate_contraction_eq k σ j f g x hfg w
end NSP14.Tests.KoszulExteriorMap
