module

public import NSP14.Homological.ModuleProducts
public import NSP14.Homological.HomologyRanks

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u w
variable (R : Type u) [CommRing R] (r : R)

noncomputable def scalarConeZeroIso (K : ChainComplex (ModuleCat.{w} R) ℕ) :
    ((scalarConeFunctor R r).obj K).X 0 ≅ K.X 0 :=
  homotopyCofiber.XIso (r • 𝟙 K) 0 (by intro h; change _+1=0 at h; omega)

theorem scalarConePieceEquiv_natural {K L : ChainComplex (ModuleCat.{w} R) ℕ} (f : K ⟶ L)
    (i : ℕ) (a : ((scalarConeFunctor R r).obj K).X (i+1)) :
    scalarConePieceEquiv L r i (((scalarConeFunctor R r).map f).f (i+1) a) =
      (f.f i (scalarConePieceEquiv K r i a).1, f.f (i+1) (scalarConePieceEquiv K r i a).2) := by
  apply Prod.ext
  · exact congrArg (fun g => g.hom a) (scalarCone_map_fst R r f i)
  · exact congrArg (fun g => g.hom a) (scalarCone_map_snd R r f (i+1))

noncomputable def scalarConeShortComplexZeroIso
    (S : ShortComplex (ChainComplex (ModuleCat.{w} R) ℕ)) :
    (S.map (scalarConeFunctor R r)).map (eval _ _ 0) ≅ S.map (eval _ _ 0) :=
  ShortComplex.isoMk (scalarConeZeroIso R r S.X₁) (scalarConeZeroIso R r S.X₂)
    (scalarConeZeroIso R r S.X₃)
    (scalarCone_map_snd R r S.f 0) (scalarCone_map_snd R r S.g 0)

noncomputable def scalarConeShortComplexSuccIso
    (S : ShortComplex (ChainComplex (ModuleCat.{w} R) ℕ)) (i : ℕ) :
    (S.map (scalarConeFunctor R r)).map (eval _ _ (i+1)) ≅
      moduleProductShortComplex (S.map (eval _ _ i)) (S.map (eval _ _ (i+1))) :=
  ShortComplex.isoMk (scalarConePieceEquiv S.X₁ r i).toModuleIso
    (scalarConePieceEquiv S.X₂ r i).toModuleIso (scalarConePieceEquiv S.X₃ r i).toModuleIso
    (by apply ModuleCat.hom_ext; ext a; exact (scalarConePieceEquiv_natural R r S.f i a).symm)
    (by apply ModuleCat.hom_ext; ext a; exact (scalarConePieceEquiv_natural R r S.g i a).symm)

theorem scalarCone_shortExact
    (S : ShortComplex (ChainComplex (ModuleCat.{w} R) ℕ)) (hS : S.ShortExact) :
    (S.map (scalarConeFunctor R r)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  have hs := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS
  cases i with
  | zero => exact ShortComplex.shortExact_of_iso (scalarConeShortComplexZeroIso R r S).symm (hs 0)
  | succ i =>
    exact ShortComplex.shortExact_of_iso (scalarConeShortComplexSuccIso R r S i).symm
      (moduleProductShortExact _ _ (hs i) (hs (i+1)))

variable (k σ : Type u) [Field k]

theorem koszul_shortExact (xs : List σ) (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
    (hS : S.ShortExact) : (S.map (koszulFunctor k σ xs)).ShortExact := by
  induction xs with
  | nil =>
    change (S.map (ChainComplex.single₀ _)).ShortExact
    let : Mono S.f := hS.mono_f
    let : Epi S.g := hS.epi_g
    exact hS.map _
  | cons x xs ih =>
    change ((S.map (koszulFunctor k σ xs)).map (scalarConeFunctor (VariableRing k σ) (MvPolynomial.X x))).ShortExact
    exact scalarCone_shortExact (VariableRing k σ) (MvPolynomial.X x) _ ih

/-- Connecting map of the actual Koszul short exact sequence, with adjacent indices. -/
noncomputable def koszulConnecting (xs : List σ) (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
    (hS : S.ShortExact) (i : ℕ) :
    ((koszulFunctor k σ xs).obj S.X₃).homology (i+1) ⟶
      ((koszulFunctor k σ xs).obj S.X₁).homology i :=
  (koszul_shortExact k σ xs S hS).δ (i+1) i rfl

end NSP14.Homological
