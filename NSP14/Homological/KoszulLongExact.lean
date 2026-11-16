module

public import NSP14.Homological.KoszulTorNaturality

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace NSP14.Homological

universe u
variable (k σ : Type u) [Field k] [Fintype σ]

@[implicit_reducible]
noncomputable def ordinaryTorFunctor (i : ℕ) :
    ModuleCat.{u} (VariableRing k σ) ⥤ ModuleCat.{u} (VariableRing k σ) :=
  CategoryTheory.Tor (ModuleCat (VariableRing k σ)) i ⋙
    (evaluation (ModuleCat (VariableRing k σ)) (ModuleCat (VariableRing k σ))).obj (residueField k σ)

/-- A natural, ordinary-Tor comparison, retaining the original variable differential. -/
noncomputable def ordinaryTorKoszulNatIso (i : ℕ) :
    ordinaryTorFunctor k σ i ≅ koszulHomologyFunctor k σ (variableList k σ) i :=
  NatIso.ofComponents (fun M => torKoszulIso k σ M i) (fun f => torKoszulIso_naturality k σ f i)

noncomputable instance ordinaryTorFunctor_additive (i : ℕ) : (ordinaryTorFunctor k σ i).Additive := by
  let : (koszulHomologyFunctor k σ (variableList k σ) i).Additive :=
    inferInstanceAs ((koszulFunctor k σ (variableList k σ) ⋙ homologyFunctor _ (ComplexShape.down ℕ) i).Additive)
  exact Functor.additive_of_iso (ordinaryTorKoszulNatIso k σ i).symm

noncomputable def torConnecting (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
    (hS : S.ShortExact) (i : ℕ) :
    (ordinaryTorFunctor k σ (i+1)).obj S.X₃ ⟶ (ordinaryTorFunctor k σ i).obj S.X₁ :=
  (torKoszulIso k σ S.X₃ (i+1)).hom ≫ koszulConnecting k σ (variableList k σ) S hS i ≫
    (torKoszulIso k σ S.X₁ i).inv

theorem tor_exact_middle (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
    (hS : S.ShortExact) (i : ℕ) : (S.map (ordinaryTorFunctor k σ i)).Exact := by
  have hs := (koszul_shortExact k σ (variableList k σ) S hS).homology_exact₂ i
  exact ShortComplex.exact_of_iso (S.mapNatIso (ordinaryTorKoszulNatIso k σ i)).symm hs

@[reassoc (attr := simp)]
theorem torConnecting_comp (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
    (hS : S.ShortExact) (i : ℕ) : torConnecting k σ S hS i ≫ (ordinaryTorFunctor k σ i).map S.f=0 := by
  have hf := (NatIso.naturality_2 (ordinaryTorKoszulNatIso k σ i) S.f).symm
  change (ordinaryTorFunctor k σ i).map S.f =
    (torKoszulIso k σ S.X₁ i).hom ≫ (koszulHomologyFunctor k σ (variableList k σ) i).map S.f ≫
      (torKoszulIso k σ S.X₂ i).inv at hf
  rw [hf]
  dsimp only [torConnecting]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  have hz : koszulConnecting k σ (variableList k σ) S hS i ≫
      (koszulHomologyFunctor k σ (variableList k σ) i).map S.f=0 :=
    (koszul_shortExact k σ (variableList k σ) S hS).δ_comp (i+1) i rfl
  rw [← Category.assoc _ _ (torKoszulIso k σ S.X₂ i).inv, hz]
  simp

@[reassoc (attr := simp)]
theorem comp_torConnecting (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
    (hS : S.ShortExact) (i : ℕ) : (ordinaryTorFunctor k σ (i+1)).map S.g ≫ torConnecting k σ S hS i=0 := by
  have hg := (NatIso.naturality_2 (ordinaryTorKoszulNatIso k σ (i+1)) S.g).symm
  change (ordinaryTorFunctor k σ (i+1)).map S.g =
    (torKoszulIso k σ S.X₂ (i+1)).hom ≫ (koszulHomologyFunctor k σ (variableList k σ) (i+1)).map S.g ≫
      (torKoszulIso k σ S.X₃ (i+1)).inv at hg
  rw [hg]
  dsimp only [torConnecting]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  have hz : (koszulHomologyFunctor k σ (variableList k σ) (i+1)).map S.g ≫
      koszulConnecting k σ (variableList k σ) S hS i=0 :=
    (koszul_shortExact k σ (variableList k σ) S hS).comp_δ (i+1) i rfl
  rw [← Category.assoc _ _ (torKoszulIso k σ S.X₁ i).inv, hz]
  simp

theorem tor_exact_connecting_left (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
    (hS : S.ShortExact) (i : ℕ) :
    (ShortComplex.mk _ _ (torConnecting_comp k σ S hS i)).Exact := by
  let hK := koszul_shortExact k σ (variableList k σ) S hS
  let e : ShortComplex.mk _ _ (torConnecting_comp k σ S hS i) ≅
      ShortComplex.mk _ _ (hK.δ_comp (i+1) i rfl) :=
    ShortComplex.isoMk (torKoszulIso k σ S.X₃ (i+1)) (torKoszulIso k σ S.X₁ i)
      (torKoszulIso k σ S.X₂ i) (by simp [torConnecting,koszulConnecting])
      (torKoszulIso_naturality k σ S.f i).symm
  exact ShortComplex.exact_of_iso e.symm (hK.homology_exact₁ (i+1) i rfl)

theorem tor_exact_connecting_right (S : ShortComplex (ModuleCat.{u} (VariableRing k σ)))
    (hS : S.ShortExact) (i : ℕ) :
    (ShortComplex.mk _ _ (comp_torConnecting k σ S hS i)).Exact := by
  let hK := koszul_shortExact k σ (variableList k σ) S hS
  let e : ShortComplex.mk _ _ (comp_torConnecting k σ S hS i) ≅
      ShortComplex.mk _ _ (hK.comp_δ (i+1) i rfl) :=
    ShortComplex.isoMk (torKoszulIso k σ S.X₂ (i+1)) (torKoszulIso k σ S.X₃ (i+1))
      (torKoszulIso k σ S.X₁ i) (torKoszulIso_naturality k σ S.g (i+1)).symm
      (by simp [torConnecting,koszulConnecting])
  exact ShortComplex.exact_of_iso e.symm (hK.homology_exact₃ (i+1) i rfl)

end NSP14.Homological
