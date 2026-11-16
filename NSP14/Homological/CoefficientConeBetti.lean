module
public import NSP14.Homological.CoefficientKoszulCons
public import NSP14.Homological.FullListBetti
@[expose] public section
open CategoryTheory HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

noncomputable def coefficientActionCone (xs : List σ)
    (M : ModuleCat.{u} (VariableRing k σ)) (f : M ⟶ M) : ChainComplex (ModuleCat.{u} k) ℕ :=
  homotopyCofiber ((coefficientKoszulListFunctor k σ xs).map f)

/-- Ordinary Tor is computed by the actual cone when the listed first
variable is the specified actual endomorphism. -/
theorem coefficientCone_Euler (x : σ) (xs : List σ)
    (hall : ∀ t,t ∈ x::xs) (hxs : (x::xs).Nodup)
    (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M]
    (f : M ⟶ M) (hf : f=(MvPolynomial.X x : VariableRing k σ) • 𝟙 M) (j : ℕ) :
    complexEuler k (homotopyCofiber ((coefficientKoszulListFunctor k σ xs).map f)) j=
      bettiEuler k σ M j := by
  let F := coefficientKoszulListFunctor k σ xs
  let Φ : (M ⟶ M) → ChainComplex (ModuleCat.{u} k) ℕ := fun q => homotopyCofiber (F.map q)
  let e := coefficientKoszulListConsIso k σ x xs M ≪≫ eqToIso (congrArg Φ hf.symm)
  calc
    _ = complexEuler k ((coefficientKoszulListFunctor k σ (x::xs)).obj M) j :=
      (complexEuler_iso k e j).symm
    _ = _ := fullList_complexEuler k σ (x::xs) hall hxs M j

theorem coefficientActionCone_Euler (x : σ) (xs : List σ)
    (hall : ∀ t,t ∈ x::xs) (hxs : (x::xs).Nodup)
    (M : ModuleCat.{u} (VariableRing k σ)) [Module.Finite (VariableRing k σ) M]
    (f : M ⟶ M) (hf : f=(MvPolynomial.X x : VariableRing k σ) • 𝟙 M) (j : ℕ) :
    complexEuler k (coefficientActionCone k σ xs M f) j=bettiEuler k σ M j :=
  coefficientCone_Euler k σ x xs hall hxs M f hf j
end NSP14.Homological
