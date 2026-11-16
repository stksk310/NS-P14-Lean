module
public import NSP14.Homological.KoszulSlotGrading
public import NSP14.Homological.HomogeneousBasisPieces
public import NSP14.Homological.GradedKoszulPieces
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Homological
variable (k σ : Type) [Field k] {J : Type}
  (M : ModuleCat (VariableRing k σ)) (G : GradedPolynomialModule k σ M)
  (b : Module.Basis J k (coefficientModule k σ M)) (deg : J → ℤ)
  (hb : ∀ a,b a ∈ G.degreeSpace (deg a))

/-- The actual internal-degree chain basis, obtained by restricting the
actual homogeneous coefficient/slot basis; no Artinian hypothesis is used. -/
noncomputable def gradedKoszulSpaceBasis (xs : List σ) (t : ℤ) (i : ℕ) :
    Module.Basis {a : KoszulSlot xs.length i × J //deg a.2=t-(i:ℤ)} k
      (gradedKoszulSpace k σ M G xs t i) :=
  (homogeneousPieceBasis k σ ((koszulList k σ xs M).X i) (koszulChainGrading k σ M G xs i)
    (koszulSlotBasis k σ M b xs i) (fun a => deg a.2)
    (koszulSlotBasis_homogeneous k σ M G b deg hb xs i) (t-(i:ℤ))).map
      (gradedKoszulSpaceEquiv k σ M G xs t i)

include hb in
theorem gradedKoszulSpaceBasis_inclusion (xs : List σ) (t : ℤ) (i : ℕ)
    (a : {a : KoszulSlot xs.length i × J //deg a.2=t-(i:ℤ)}) :
    (gradedKoszulSpaceBasis k σ M G b deg hb xs t i a).val=koszulSlotBasis k σ M b xs i a.val := by
  unfold gradedKoszulSpaceBasis
  rw [Module.Basis.map_apply]
  exact homogeneousPieceBasis_inclusion k σ ((koszulList k σ xs M).X i) (koszulChainGrading k σ M G xs i)
    (koszulSlotBasis k σ M b xs i) (fun a => deg a.2)
    (koszulSlotBasis_homogeneous k σ M G b deg hb xs i) (t-(i:ℤ)) a

include hb in
theorem gradedKoszulSpaceBasis_repr (xs : List σ) (t : ℤ) (i : ℕ)
    (x : gradedKoszulSpace k σ M G xs t i)
    (a : {a : KoszulSlot xs.length i × J //deg a.2=t-(i:ℤ)}) :
    (gradedKoszulSpaceBasis k σ M G b deg hb xs t i).repr x a=
      (koszulSlotBasis k σ M b xs i).repr x.val a.val := by
  let B := gradedKoszulSpaceBasis k σ M G b deg hb xs t i
  let C := koszulSlotBasis k σ M b xs i
  have hf : B.coord a=(C.coord a.val).comp (gradedKoszulSpace k σ M G xs t i).subtype := by
    apply B.ext
    intro j
    change B.repr (B j) a=C.repr (B j).val a.val
    rw [gradedKoszulSpaceBasis_inclusion]
    change B.repr (B j) a=C.repr (C j.val) a.val
    by_cases he : j=a
    · subst j
      simp only [Module.Basis.repr_self_apply,ite_true]
    · have hv : j.val ≠ a.val := fun h => he (Subtype.ext h)
      simp only [Module.Basis.repr_self_apply,ite_eq_right he,ite_eq_right hv]
  exact LinearMap.congr_fun hf x

include hb in
theorem gradedKoszulSpace_finite_of_basis (xs : List σ) (t : ℤ) (i : ℕ)
    [Finite {a : KoszulSlot xs.length i × J //deg a.2=t-(i:ℤ)}] :
    Module.Finite k (gradedKoszulSpace k σ M G xs t i) := by
  let : Fintype {a : KoszulSlot xs.length i × J //deg a.2=t-(i:ℤ)} := Fintype.ofFinite _
  exact Module.Finite.of_basis (gradedKoszulSpaceBasis k σ M G b deg hb xs t i)
end NSP14.Homological
