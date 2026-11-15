module
public import NSP14.Homological.IdealAdjoining
public import NSP14.Homological.KoszulAnnihilation
public import NSP14.Homological.KoszulLinearity
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (k σ : Type u) [Field k] [Fintype σ]

/-- A variable multiple of any actual module map induces zero on actual
coefficient Koszul homology, by the constructed contraction. -/
theorem coefficientKoszul_variable_smul_zero
    {M N : ModuleCat.{u} (VariableRing k σ)} (f : M ⟶ N) (x : σ) (i : ℕ) :
    homologyMap ((coefficientKoszulFunctor k σ).map
      ((MvPolynomial.X x : VariableRing k σ) • f)) i=0 := by
  let F := koszulFunctor k σ (variableList k σ)
  have he : F.map ((MvPolynomial.X x : VariableRing k σ) • f)=
      F.map f ≫ ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (koszulList k σ (variableList k σ) N)) := by
    change F.map ((MvPolynomial.X x : VariableRing k σ) • f)=
      F.map f ≫ ((MvPolynomial.X x : VariableRing k σ) • 𝟙 (F.obj N))
    rw [F.map_smul,Linear.comp_smul,Category.comp_id]
  have hh := (koszulVariableHomotopy k σ N x).compLeft (F.map f)
  have h : Homotopy (F.map ((MvPolynomial.X x : VariableRing k σ) • f)) 0 :=
    (Homotopy.ofEq he).trans (hh.trans (Homotopy.ofEq (by simp)))
  have hc := ((ModuleCat.restrictScalars (algebraMap k (VariableRing k σ))).mapHomotopy h).homologyMap_eq i
  simpa only [coefficientKoszulFunctor,Functor.comp_map,F,Functor.map_zero,homologyMap_zero] using hc

/-- The ordinary Tor additivity needed for a linear-quotient step is
deduced from the actual colon sequence and an actual variable factor. -/
theorem idealAdjoin_betti_additivity (J : Ideal (VariableRing k σ))
    (g h : VariableRing k σ) (x : σ) (he : g=MvPolynomial.X x*h)
    (hc : J.colon {g} ≤ J.colon {h}) (i : ℕ) :
    totalBetti k σ (ModuleCat.of (VariableRing k σ) ((VariableRing k σ) ⧸ (J ⊔ Ideal.span {g}))) (i+1)=
      totalBetti k σ (ModuleCat.of (VariableRing k σ) ((VariableRing k σ) ⧸ J)) (i+1)+
      totalBetti k σ (ModuleCat.of (VariableRing k σ) ((VariableRing k σ) ⧸ J.colon {g})) i := by
  let : Module.Finite (VariableRing k σ) (idealAdjoinSequence (VariableRing k σ) J g).X₁ := by
    change Module.Finite (VariableRing k σ) ((VariableRing k σ) ⧸ J.colon {g})
    infer_instance
  let : Module.Finite (VariableRing k σ) (idealAdjoinSequence (VariableRing k σ) J g).X₂ := by
    change Module.Finite (VariableRing k σ) ((VariableRing k σ) ⧸ J)
    infer_instance
  let : Module.Finite (VariableRing k σ) (idealAdjoinSequence (VariableRing k σ) J g).X₃ := by
    change Module.Finite (VariableRing k σ) ((VariableRing k σ) ⧸ (J ⊔ Ideal.span {g}))
    infer_instance
  apply koszul_quotient_betti_additivity k σ (idealAdjoinSequence (VariableRing k σ) J g)
    (idealAdjoinSequence_shortExact (VariableRing k σ) J g) i
  intro j
  change homologyMap ((coefficientKoszulFunctor k σ).map (idealAdjoinLeft (VariableRing k σ) J g)) j=0
  rw [idealAdjoinLeft_factor (VariableRing k σ) J g (MvPolynomial.X x) h he hc]
  exact coefficientKoszul_variable_smul_zero k σ _ x j

end NSP14.Homological
