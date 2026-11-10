module

public import NSP14.Homological.KoszulGrading

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k]
variable (M : ModuleCat.{u} (VariableRing k σ)) (G : GradedPolynomialModule k σ M)

/-- The grading inclusion is the actual cofiber inclusion, not an abstract degree label. -/
theorem koszulChainGrading_inclusion_zero (x : σ) (xs : List σ) (q : ℤ)
    (a : (koszulChainGrading k σ M G xs 0).piece q) :
    (koszulChainGrading k σ M G (x::xs) 0).inclusion q a=
      homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) 0
        ((koszulChainGrading k σ M G xs 0).inclusion q a) := by
  rfl

theorem koszulChainGrading_inclusion_succ (x : σ) (xs : List σ) (i : ℕ) (q : ℤ)
    (a : (koszulChainGrading k σ M G xs i).piece q)
    (b : (koszulChainGrading k σ M G xs (i+1)).piece q) :
    (koszulChainGrading k σ M G (x::xs) (i+1)).inclusion q (a,b)=
      homotopyCofiber.inlX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) i (i+1) (natDownStep i)
        ((koszulChainGrading k σ M G xs i).inclusion q a) +
      homotopyCofiber.inrX ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ xs M)) (i+1)
        ((koszulChainGrading k σ M G xs (i+1)).inclusion q b) := by
  rfl

end NSP14.Homological
