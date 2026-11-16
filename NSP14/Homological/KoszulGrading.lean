module

public import NSP14.Homological.GradedModule
public import NSP14.Homological.KoszulChainDimension

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped DirectSum

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k]

/-- Coefficient-degree grading on the actual chain module. Internal degree is q+i. -/
noncomputable def koszulChainGrading (M : ModuleCat.{u} (VariableRing k σ))
    (G : GradedPolynomialModule k σ M) :
    ∀ (xs : List σ) i, GradedPolynomialModule k σ ((koszulList k σ xs M).X i)
  | [],0 => G
  | [],i+1 => .zero _ (koszul_piece_isZero_of_gt k σ [] M (i+1) (by simp))
  | x::xs,0 => (koszulChainGrading M G xs 0).transport
      (scalarConeZeroIso (VariableRing k σ) (MvPolynomial.X x) (koszulList k σ xs M)).symm
  | x::xs,i+1 => ((koszulChainGrading M G xs i).prod (koszulChainGrading M G xs (i+1))).transport
      (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i).symm.toModuleIso

namespace GradedPolynomialModule

variable {k σ} {M N : ModuleCat.{u} (VariableRing k σ)}

noncomputable def degreeSpace (G : GradedPolynomialModule k σ M) (q : ℤ) : Submodule k (coefficientModule k σ M) :=
  (G.inclusion q).range

theorem variable_mem (G : GradedPolynomialModule k σ M) (q : ℤ) (x : σ)
    {a : coefficientModule k σ M} (ha : a∈G.degreeSpace q) :
    (MvPolynomial.X x : VariableRing k σ) • a∈G.degreeSpace (q+1) := by
  obtain ⟨b,rfl⟩ := ha
  exact ⟨G.variableMap x q b,G.variable_commutes x q b⟩

@[simp]
theorem transport_mem (G : GradedPolynomialModule k σ M) (e : M ≅ N) (q : ℤ)
    (a : coefficientModule k σ N) :
    a∈(G.transport e).degreeSpace q ↔ e.inv a∈G.degreeSpace q := by
  constructor
  · rintro ⟨b,rfl⟩
    refine ⟨b,?_⟩
    change G.inclusion q b = e.inv (e.hom (G.inclusion q b))
    simp
  · rintro ⟨b,hb⟩
    refine ⟨b,?_⟩
    change e.hom (G.inclusion q b)=a
    rw [hb]
    simp

@[simp]
theorem prod_mem (G : GradedPolynomialModule k σ M) (H : GradedPolynomialModule k σ N)
    (q : ℤ) (a : coefficientModule k σ (ModuleCat.of (VariableRing k σ) (M×N))) :
    a∈(G.prod H).degreeSpace q ↔
      a.1∈G.degreeSpace q ∧ a.2∈H.degreeSpace q := by
  constructor
  · rintro ⟨b,rfl⟩
    exact ⟨⟨b.1,rfl⟩,⟨b.2,rfl⟩⟩
  · rintro ⟨⟨b,hb⟩,⟨c,hc⟩⟩
    exact ⟨(b,c),Prod.ext hb hc⟩

end GradedPolynomialModule

/-- The signed actual differential increases coefficient degree by one.
This is the homogeneity statement behind preservation of internal degree q+i. -/
theorem koszul_d_homogeneous (M : ModuleCat.{u} (VariableRing k σ))
    (G : GradedPolynomialModule k σ M) (xs : List σ) (i : ℕ) (q : ℤ)
    (a : coefficientModule k σ ((koszulList k σ xs M).X (i+1)))
    (ha : a∈(koszulChainGrading k σ M G xs (i+1)).degreeSpace q) :
    (koszulList k σ xs M).d (i+1) i a∈(koszulChainGrading k σ M G xs i).degreeSpace (q+1) := by
  induction xs generalizing i with
  | nil =>
    have hz : a=0 := (ModuleCat.subsingleton_of_isZero
      (koszul_piece_isZero_of_gt k σ [] M (i+1) (by simp))).elim _ _
    rw [hz,map_zero]
    exact Submodule.zero_mem _
  | cons x xs ih =>
    have ha' : (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i a).1∈
          (koszulChainGrading k σ M G xs i).degreeSpace q ∧
        (scalarConePieceEquiv (koszulList k σ xs M) (MvPolynomial.X x) i a).2∈
          (koszulChainGrading k σ M G xs (i+1)).degreeSpace q := by
      rw [koszulChainGrading,GradedPolynomialModule.transport_mem] at ha
      exact (GradedPolynomialModule.prod_mem _ _ _ _).mp ha
    cases i with
    | zero =>
      rw [koszulChainGrading,GradedPolynomialModule.transport_mem]
      have he := congrArg (fun f => f.hom a) (koszul_cons_d_second k σ x xs M 0)
      change (scalarConeZeroIso (VariableRing k σ) (MvPolynomial.X x) (koszulList k σ xs M)).hom
        ((koszulList k σ (x::xs) M).d 1 0 a)∈_
      change koszulSecondProjection k σ x xs M 0 ((koszulList k σ (x::xs) M).d 1 0 a)∈_
      simp only [ModuleCat.hom_comp,LinearMap.comp_apply] at he
      change _ = (MvPolynomial.X x : VariableRing k σ) •
        koszulFirstProjection k σ x xs M 0 a +
          (koszulList k σ xs M).d 1 0 (koszulSecondProjection k σ x xs M 1 a) at he
      erw [he]
      exact Submodule.add_mem _ ((koszulChainGrading k σ M G xs 0).variable_mem q x ha'.1)
        (ih 0 _ ha'.2)
    | succ i =>
      rw [koszulChainGrading,GradedPolynomialModule.transport_mem,GradedPolynomialModule.prod_mem]
      constructor
      · have he := congrArg (fun f => f.hom a) (koszul_cons_d_first k σ x xs M i)
        simp only [ModuleCat.hom_comp,LinearMap.comp_apply] at he
        change _ = -((koszulList k σ xs M).d (i+1) i
          (koszulFirstProjection k σ x xs M (i+1) a)) at he
        change koszulFirstProjection k σ x xs M i ((koszulList k σ (x::xs) M).d (i+2) (i+1) a)∈_
        erw [he]
        exact Submodule.neg_mem _ (ih i _ ha'.1)
      · have he := congrArg (fun f => f.hom a) (koszul_cons_d_second k σ x xs M (i+1))
        simp only [ModuleCat.hom_comp,LinearMap.comp_apply] at he
        change _ = (MvPolynomial.X x : VariableRing k σ) •
          koszulFirstProjection k σ x xs M (i+1) a +
            (koszulList k σ xs M).d (i+2) (i+1) (koszulSecondProjection k σ x xs M (i+2) a) at he
        change koszulSecondProjection k σ x xs M (i+1) ((koszulList k σ (x::xs) M).d (i+2) (i+1) a)∈_
        erw [he]
        exact Submodule.add_mem _ ((koszulChainGrading k σ M G xs (i+1)).variable_mem q x ha'.1)
          (ih (i+1) _ ha'.2)

end NSP14.Homological
