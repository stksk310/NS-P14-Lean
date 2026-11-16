module
public import NSP14.Lex.DistractionIdeal
public import NSP14.Homological.KoszulExteriorMap
@[expose] public section
open scoped Classical
open NSP14.Homological
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

def genericDistractionWedgeEquiv (j : ℕ) (a : Fin q →₀ ℕ) :
    (⋀[GenericDistractionField k q]^j (Fin q → GenericDistractionField k q)) ≃ₗ[GenericDistractionField k q]
      (⋀[GenericDistractionField k q]^j (Fin q → GenericDistractionField k q)) :=
  exteriorPowerLinearEquiv (GenericDistractionField k q) j (genericFieldLinearEquiv k q a)

theorem genericDistractionWedge_contraction (j : ℕ) (a : Fin q →₀ ℕ)
    (φ : Module.Dual (GenericDistractionField k q) (Fin q → GenericDistractionField k q))
    (w : ⋀[GenericDistractionField k q]^(j+1) (Fin q → GenericDistractionField k q)) :
    koszulExteriorContraction _ _ j φ (genericDistractionWedgeEquiv k q (j+1) a w)=
      genericDistractionWedgeEquiv k q j a
        (koszulExteriorContraction _ _ j (φ.comp (genericFieldLinearEquiv k q a).toLinearMap) w) :=
  koszulExteriorContraction_naturality _ _ j _ φ w

theorem genericFieldLinearEquiv_step_other (a : Fin q →₀ ℕ) (i r : Fin q) (hri : r≠i) :
    genericFieldLinearEquiv k q (a+Finsupp.single i 1) (Pi.single r 1)=
      genericFieldLinearEquiv k q a (Pi.single r 1) := by
  funext x
  rw [genericFieldLinearEquiv_single,genericFieldLinearEquiv_single]
  simp only [genericFieldMatrix,genericRawMatrix,Matrix.map_apply,Finsupp.add_apply,
    Finsupp.single_eq_of_ne hri,add_zero]

theorem genericDistractionWedge_step_contraction (j : ℕ) (a : Fin q →₀ ℕ) (i : Fin q)
    (w : ⋀[GenericDistractionField k q]^(j+1) (Fin q → GenericDistractionField k q)) :
    genericDistractionWedgeEquiv k q j a
      (koszulExteriorContraction _ _ j (LinearMap.proj i) w)=
    genericDistractionWedgeEquiv k q j (a+Finsupp.single i 1)
      (koszulExteriorContraction _ _ j (LinearMap.proj i) w) := by
  change exteriorPower.map j (genericFieldLinearEquiv k q a).toLinearMap
      (koszulExteriorContraction _ _ j (LinearMap.proj i) w)=
    exteriorPower.map j (genericFieldLinearEquiv k q (a+Finsupp.single i 1)).toLinearMap
      (koszulExteriorContraction _ _ j (LinearMap.proj i) w)
  refine koszulExteriorMap_coordinate_contraction_eq (GenericDistractionField k q) (Fin q) j
    (genericFieldLinearEquiv k q a).toLinearMap
    (genericFieldLinearEquiv k q (a+Finsupp.single i 1)).toLinearMap i ?_ w
  intro r hr
  simp only [LinearEquiv.coe_coe]
  convert (genericFieldLinearEquiv_step_other k q a i r hr).symm using 1 <;>
    congr 1 <;> funext x <;>
      (by_cases hx : x=r <;> simp only [Pi.single_apply,hx,ite_true,ite_false])
end NSP14.Lex
