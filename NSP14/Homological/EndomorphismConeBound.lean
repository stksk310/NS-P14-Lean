module
public import NSP14.Homological.ConeSuspension
public import NSP14.Homological.FilteredComparison
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace NSP14.Homological
universe u
variable (R : Type u) [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ) (f : K ⟶ K)

noncomputable def endomorphismConeDiagram : zeroIdSequence R K ⟶ idZeroSequence R K :=
  ShortComplex.homMk 0 f 0 (by simp [zeroIdSequence,idZeroSequence]) (by simp [zeroIdSequence,idZeroSequence])
noncomputable def endomorphismConeSequence : ShortComplex (ChainComplex (ModuleCat.{u} R) ℕ) :=
  coneDiagram R (endomorphismConeDiagram R K f)

theorem endomorphismConeSequence_shortExact : (endomorphismConeSequence R K f).ShortExact :=
  coneDiagram_shortExact R _ (zeroIdSequence_shortExact R K) (idZeroSequence_shortExact R K)

noncomputable def endomorphismConeFirstIso : (endomorphismConeSequence R K f).X₁ ≅ K :=
  zeroArrowConeIso R K

noncomputable def endomorphismConeThirdIso : (endomorphismConeSequence R K f).X₃ ≅ coneSuspension R K := Iso.refl _

variable (k : Type u) [Field k] (J : ChainComplex (ModuleCat.{u} k) ℕ) (g : J ⟶ J)
  [∀ i,Module.Finite k (J.homology i)]

noncomputable def endomorphismConeFirstHomologyIso (i : ℕ) :
    (endomorphismConeSequence k J g).X₁.homology i ≅ J.homology i :=
  (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (endomorphismConeFirstIso k J g)

noncomputable instance endomorphismConeFirst_finite (i : ℕ) :
    Module.Finite k ((endomorphismConeSequence k J g).X₁.homology i) :=
  Module.Finite.equiv (endomorphismConeFirstHomologyIso k J g i).symm.toLinearEquiv

noncomputable instance endomorphismConeThird_finite (i : ℕ) :
    Module.Finite k ((endomorphismConeSequence k J g).X₃.homology i) := by
  cases i with
  | zero =>
    have : Subsingleton ((endomorphismConeSequence k J g).X₃.homology 0) :=
      ModuleCat.subsingleton_of_isZero (coneSuspension_homology_zero k J)
    infer_instance
  | succ i => exact Module.Finite.equiv (coneSuspensionHomologyIso k J i).symm.toLinearEquiv

theorem endomorphismCone_homology_finite (i : ℕ) :
    Module.Finite k ((homotopyCofiber g).homology i) :=
  homology_finite_of_ends k (endomorphismConeSequence k J g) (endomorphismConeSequence_shortExact k J g) i

/-- The cone estimate only uses finite homology, even for infinite chains. -/
theorem endomorphismCone_finrank_le (i : ℕ) :
    Module.finrank k ((homotopyCofiber g).homology i) ≤ Module.finrank k (J.homology i)+
      (if i=0 then 0 else Module.finrank k (J.homology (i-1))) := by
  have h := homology_finrank_bound k (endomorphismConeSequence k J g) (endomorphismConeSequence_shortExact k J g) i
  rw [(endomorphismConeFirstHomologyIso k J g i).toLinearEquiv.finrank_eq] at h
  change Module.finrank k ((homotopyCofiber g).homology i) ≤ Module.finrank k (J.homology i)+
    Module.finrank k ((coneSuspension k J).homology i) at h
  cases i with
  | zero =>
    have : Subsingleton ((coneSuspension k J).homology 0) :=
      ModuleCat.subsingleton_of_isZero (coneSuspension_homology_zero k J)
    have hz : Module.finrank k ((coneSuspension k J).homology 0)=0 := Module.finrank_zero_of_subsingleton
    rw [hz] at h
    simpa using h
  | succ i =>
    rw [(coneSuspensionHomologyIso k J i).toLinearEquiv.finrank_eq] at h
    simpa using h
end NSP14.Homological
