module
public import NSP14.Homological.AcyclicQuotient
public import NSP14.Homological.ComplexEuler
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex ZeroObject
namespace NSP14.Homological
universe u
variable (k : Type u) [Field k]

theorem complexEuler_epiCone_succ (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ))
    (hS : S.ShortExact) (j : ℕ) :
    complexEuler k (homotopyCofiber S.g) (j+1)=complexEuler k S.X₁ j := by
  have hz : Module.finrank k ((homotopyCofiber S.g).homology 0)=0 := by
    let : Subsingleton ((homotopyCofiber S.g).homology 0) :=
      ModuleCat.subsingleton_of_isZero (epiCone_homology_zero k S hS)
    exact Module.finrank_zero_of_subsingleton
  have hs (i : ℕ) := (epiConeHomologySuccIso k S hS i).toLinearEquiv.finrank_eq
  induction j with
  | zero => rw [complexEuler_succ,complexEuler_zero,complexEuler_zero,hz,hs];simp
  | succ j ih => rw [complexEuler_succ,ih,complexEuler_succ,hs]

theorem epiConeHomology_finite (S : ShortComplex (ChainComplex (ModuleCat.{u} k) ℕ))
    (hS : S.ShortExact) [∀ i,Module.Finite k (S.X₁.homology i)] (i : ℕ) :
    Module.Finite k ((homotopyCofiber S.g).homology i) := by
  cases i with
  | zero =>
    let : Subsingleton ((homotopyCofiber S.g).homology 0) :=
      ModuleCat.subsingleton_of_isZero (epiCone_homology_zero k S hS)
    infer_instance
  | succ i => exact Module.Finite.equiv (epiConeHomologySuccIso k S hS i).symm.toLinearEquiv

variable {K G I A : ChainComplex (ModuleCat.{u} k) ℕ}
  (f : K ⟶ G) (g : G ⟶ I) (a : I ⟶ G) (b : G ⟶ A)
  (hfg : f ≫ g=0) (hab : a ≫ b=0)

noncomputable def factorConeDiagram : idZeroSequence k G ⟶ ShortComplex.mk a b hab :=
  ShortComplex.homMk g (g ≫ a) 0
    (by simp [idZeroSequence]) (by simp [idZeroSequence,hab])

/-- The sharp reversed-Euler comparison for a two-term object, obtained
from two actual short exact sequences and their cones. Only the endpoint
homologies are finite; the G/I chains may be infinite dimensional. -/
theorem factorCone_Euler_comparison
    (h₁ : (ShortComplex.mk f g hfg).ShortExact) (h₂ : (ShortComplex.mk a b hab).ShortExact)
    [∀ i,Module.Finite k (K.homology i)] [∀ i,Module.Finite k (A.homology i)] (j : ℕ) :
    complexEuler k (homotopyCofiber (g ≫ a)) (j+1) ≤ complexEuler k A (j+1)+complexEuler k K j := by
  let D := coneDiagram k (factorConeDiagram k g a b hab)
  have hD := coneDiagram_shortExact k (factorConeDiagram k g a b hab)
    (idZeroSequence_shortExact k G) h₂
  let : ∀ i,Module.Finite k (D.X₁.homology i) := fun i =>
    epiConeHomology_finite k (ShortComplex.mk f g hfg) h₁ i
  let : ∀ i,Module.Finite k (D.X₃.homology i) := fun i => by
    let e : D.X₃.homology i ≅ A.homology i :=
      (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (zeroArrowConeIso k A)
    exact Module.Finite.equiv e.symm.toLinearEquiv
  have h := complexEuler_middle_le k D hD (j+1)
  have hL := complexEuler_epiCone_succ k (ShortComplex.mk f g hfg) h₁ j
  have hQ : complexEuler k D.X₃ (j+1)=complexEuler k A (j+1) :=
    complexEuler_congr k (fun i =>
      ((homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (zeroArrowConeIso k A)).toLinearEquiv.finrank_eq) _
  change complexEuler k (homotopyCofiber (g ≫ a)) (j+1) ≤
    complexEuler k (homotopyCofiber g) (j+1)+complexEuler k D.X₃ (j+1) at h
  rw [hL,hQ] at h
  exact h.trans_eq (add_comm _ _)

noncomputable def factorConeCorrection
    (h₂ : (ShortComplex.mk a b hab).ShortExact) (j : ℕ) : ℕ :=
  complexConnectingRank k (coneDiagram k (factorConeDiagram k g a b hab))
    (coneDiagram_shortExact k (factorConeDiagram k g a b hab) (idZeroSequence_shortExact k G) h₂) j

theorem factorCone_Euler_eq
    (h₁ : (ShortComplex.mk f g hfg).ShortExact) (h₂ : (ShortComplex.mk a b hab).ShortExact)
    [∀ i,Module.Finite k (K.homology i)] [∀ i,Module.Finite k (A.homology i)] (j : ℕ) :
    complexEuler k (homotopyCofiber (g ≫ a)) (j+1)=
      complexEuler k A (j+1)+complexEuler k K j-(factorConeCorrection k g a b hab h₂ (j+1) : ℤ) := by
  let D := coneDiagram k (factorConeDiagram k g a b hab)
  let hD := coneDiagram_shortExact k (factorConeDiagram k g a b hab)
    (idZeroSequence_shortExact k G) h₂
  let : ∀ i,Module.Finite k (D.X₁.homology i) := fun i =>
    epiConeHomology_finite k (ShortComplex.mk f g hfg) h₁ i
  let : ∀ i,Module.Finite k (D.X₃.homology i) := fun i => by
    let e : D.X₃.homology i ≅ A.homology i :=
      (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (zeroArrowConeIso k A)
    exact Module.Finite.equiv e.symm.toLinearEquiv
  have h := complexEuler_shortExact k D hD (j+1)
  have hL := complexEuler_epiCone_succ k (ShortComplex.mk f g hfg) h₁ j
  have hQ : complexEuler k D.X₃ (j+1)=complexEuler k A (j+1) :=
    complexEuler_congr k (fun i =>
      ((homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (zeroArrowConeIso k A)).toLinearEquiv.finrank_eq) _
  change complexEuler k (homotopyCofiber (g ≫ a)) (j+1)=
    complexEuler k (homotopyCofiber g) (j+1)+complexEuler k D.X₃ (j+1)-
      (factorConeCorrection k g a b hab h₂ (j+1) : ℤ) at h
  rw [hL,hQ] at h
  exact h.trans (congrArg (fun z : ℤ => z-(factorConeCorrection k g a b hab h₂ (j+1) : ℤ)) (add_comm _ _))

theorem factorConeCorrection_zero_of_quotient_homology_isZero
    (h₂ : (ShortComplex.mk a b hab).ShortExact) (j : ℕ) (hA : IsZero (A.homology (j+1))) :
    factorConeCorrection k g a b hab h₂ j=0 := by
  let D := coneDiagram k (factorConeDiagram k g a b hab)
  let hD := coneDiagram_shortExact k (factorConeDiagram k g a b hab)
    (idZeroSequence_shortExact k G) h₂
  have hz : IsZero (D.X₃.homology (j+1)) := IsZero.of_iso hA
    ((homologyFunctor _ (ComplexShape.down ℕ) (j+1)).mapIso (zeroArrowConeIso k A))
  have hd : hD.δ (j+1) j rfl=0 := hz.eq_of_src _ _
  unfold factorConeCorrection complexConnectingRank
  change Module.finrank k (hD.δ (j+1) j rfl).hom.range=0
  rw [hd]
  change Module.finrank k (0 : D.X₃.homology (j+1) →ₗ[k] D.X₁.homology j).range=0
  rw [LinearMap.range_zero,finrank_bot]
end NSP14.Homological
