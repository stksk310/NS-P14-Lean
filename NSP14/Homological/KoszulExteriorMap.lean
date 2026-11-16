module
public import NSP14.Homological.KoszulExterior
public import NSP14.Homological.ExteriorContraction
public import NSP14.Homological.KoszulArrowWedge
@[expose] public section
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Homological
variable (k σ : Type) [Field k] [Fintype σ]

omit [Fintype σ] in
theorem exteriorPowerLinearEquiv_coe (j : ℕ) (e : (σ → k) ≃ₗ[k] (σ → k))
    (w : ⋀[k]^j (σ → k)) :
    (exteriorPowerLinearEquiv k j e w : ExteriorAlgebra k (σ → k))=
      ExteriorAlgebra.map e.toLinearMap w.val := by
  change (exteriorPower.map j e.toLinearMap w : ExteriorAlgebra k (σ → k))=_
  exact exteriorPower.coe_map _ _

theorem koszulExteriorContraction_naturality (j : ℕ) (e : (σ → k) ≃ₗ[k] (σ → k))
    (φ : Module.Dual k (σ → k)) (w : ⋀[k]^(j+1) (σ → k)) :
    koszulExteriorContraction k σ j φ (exteriorPowerLinearEquiv k (j+1) e w)=
      exteriorPowerLinearEquiv k j e (koszulExteriorContraction k σ j (φ.comp e.toLinearMap) w) := by
  apply Subtype.ext
  rw [koszulExteriorContraction_coe,exteriorPowerLinearEquiv_coe,exteriorPowerLinearEquiv_coe,
    koszulExteriorContraction_coe,exterior_contract_map]

theorem koszulExteriorMap_basis_eq (j : ℕ) (f g : (σ → k) →ₗ[k] (σ → k))
    (s : KoszulSlot (variableList k σ).length j)
    (hfg : ∀ x∈koszulSlotWedge (variableList k σ) j s,
      f (Pi.single x 1)=g (Pi.single x 1)) :
    exteriorPower.map j f (koszulExteriorBasis (σ:=σ) k j s)=
      exteriorPower.map j g (koszulExteriorBasis (σ:=σ) k j s) := by
  rw [koszulExteriorBasis_apply]
  unfold koszulSlotExterior
  rw [exteriorPower.map_apply_ιMulti,exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  apply hfg
  change koszulSlotTuple (variableList k σ) (variableList_nodup k σ) j s i ∈
    (koszulSlotWedge (variableList k σ) j s : Set σ)
  rw [← koszulSlotTuple_range (variableList k σ) (variableList_nodup k σ) j s]
  exact ⟨i,rfl⟩

theorem koszulExteriorMap_coordinate_contraction_eq (j : ℕ)
    (f g : (σ → k) →ₗ[k] (σ → k)) (x : σ)
    (hfg : ∀ y, y≠x → f (Pi.single y 1)=g (Pi.single y 1))
    (w : ⋀[k]^(j+1) (σ → k)) :
    exteriorPower.map j f (koszulExteriorContraction k σ j (LinearMap.proj x) w)=
      exteriorPower.map j g (koszulExteriorContraction k σ j (LinearMap.proj x) w) := by
  have h : (exteriorPower.map j f).comp (koszulExteriorContraction k σ j (LinearMap.proj x))=
      (exteriorPower.map j g).comp (koszulExteriorContraction k σ j (LinearMap.proj x)) := by
    apply (koszulExteriorBasis (σ:=σ) k (j+1)).ext
    intro s
    simp only [LinearMap.comp_apply,koszulExteriorContraction_basis,map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro t _
    by_cases hz : koszulArrowScalar k (fun y : σ => Pi.single y (1:k)) (LinearMap.proj x)
        (koszulSlotArrow (variableList k σ) j s t)=0
    · simp only [hz,zero_smul]
    · have hx : x∉koszulSlotWedge (variableList k σ) j t := by
        cases ha : koszulSlotArrow (variableList k σ) j s t with
        | none => simp [ha,koszulArrowScalar] at hz
        | some a =>
          rcases a with ⟨y,sign⟩
          have hy : y=x := by
            by_contra hn
            cases sign <;> simp [ha,koszulArrowScalar,Ne.symm hn] at hz
          subst y
          exact (koszulSlotArrow_wedge _ (variableList_nodup k σ) j s t x sign ha).2.1
      congr 1
      exact koszulExteriorMap_basis_eq k σ j f g t (fun y hy => hfg y (fun he => hx (he ▸ hy)))
  exact LinearMap.congr_fun h w

theorem koszulExteriorContraction_decompose (j : ℕ) (φ : Module.Dual k (σ → k))
    (w : ⋀[k]^(j+1) (σ → k)) :
    koszulExteriorContraction k σ j φ w = ∑ x : σ,φ (Pi.single x 1) •
      koszulExteriorContraction k σ j (LinearMap.proj x) w := by
  have hφ : φ=∑ x : σ,φ (Pi.single x 1) • (LinearMap.proj x : (σ → k) →ₗ[k] k) := by
    apply (Pi.basisFun k σ).ext
    intro i
    simp [Pi.basisFun_apply,LinearMap.sum_apply,LinearMap.smul_apply,Pi.single_apply]
  apply Subtype.ext
  simp only [Submodule.coe_sum,Submodule.coe_smul,koszulExteriorContraction_coe]
  have he := congrArg (fun ψ : Module.Dual k (σ → k) => CliffordAlgebra.contractLeft ψ w.val) hφ
  simpa only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply] using he
end NSP14.Homological
