module

public import NSP14.Homological.ScalarConeMaps

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace NSP14.Homological

universe u w
variable {R : Type u} [CommRing R]

noncomputable def moduleProductShortComplex (S T : ShortComplex (ModuleCat.{w} R)) :
    ShortComplex (ModuleCat.{w} R) where
  f := ModuleCat.ofHom (S.f.hom.prodMap T.f.hom)
  g := ModuleCat.ofHom (S.g.hom.prodMap T.g.hom)
  zero := by ext x <;> simp

theorem moduleProductShortExact (S T : ShortComplex (ModuleCat.{w} R))
    (hS : S.ShortExact) (hT : T.ShortExact) : (moduleProductShortComplex S T).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff]
    rintro ⟨a,b⟩ h
    obtain ⟨u,hu⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS.exact a (congrArg Prod.fst h)
    obtain ⟨v,hv⟩ := (ShortComplex.moduleCat_exact_iff T).mp hT.exact b (congrArg Prod.snd h)
    exact ⟨(u,v),Prod.ext hu hv⟩
  · rw [ModuleCat.mono_iff_injective]
    intro a b h
    exact Prod.ext (hS.moduleCat_injective_f (congrArg Prod.fst h))
      (hT.moduleCat_injective_f (congrArg Prod.snd h))
  · rw [ModuleCat.epi_iff_surjective]
    intro a
    obtain ⟨u,hu⟩ := hS.moduleCat_surjective_g a.1
    obtain ⟨v,hv⟩ := hT.moduleCat_surjective_g a.2
    exact ⟨(u,v),Prod.ext hu hv⟩

/-- The actual two components of the cone, with their actual inclusions as inverse. -/
noncomputable def scalarConePieceEquiv (K : ChainComplex (ModuleCat.{w} R) ℕ) (r : R) (i : ℕ) :
    (HomologicalComplex.homotopyCofiber (r • 𝟙 K)).X (i+1) ≃ₗ[R] K.X i × K.X (i+1) where
  toLinearMap := (coneFirst K r i).prod (coneSecond K r (i+1))
  invFun a := HomologicalComplex.homotopyCofiber.inlX (r • 𝟙 K) i (i+1) rfl a.1 +
    HomologicalComplex.homotopyCofiber.inrX (r • 𝟙 K) (i+1) a.2
  left_inv z := (scalarCone_split K r i z).symm
  right_inv a := by
    apply Prod.ext
    · change coneFirst K r i (_+_)=_
      erw [map_add,coneFirst_inl,coneFirst_inr,add_zero]
    · change coneSecond K r (i+1) (_+_)=_
      erw [map_add,coneSecond_inl,coneSecond_inr,zero_add]

end NSP14.Homological
