module

public import NSP14.Homological.KoszulGradedMaps

@[expose] public section

open CategoryTheory HomologicalComplex

namespace NSP14.Homological

universe u
variable {L : Type u} [Field L]
variable {A B C D : ChainComplex (ModuleCat.{u} L) ℕ}

/-- Restrict the same total chain isomorphism through given componentwise degree isomorphisms.
The differential equation follows from the actual inclusions and their monicity. -/
noncomputable def complexIsoOfRestrictions (E : C ≅ D) (a : A ⟶ C) (b : B ⟶ D)
    [∀ i,Mono (b.f i)] (f : ∀ i,A.X i ≅ B.X i)
    (hf : ∀ i,(f i).hom ≫ b.f i=a.f i ≫ E.hom.f i) : A ≅ B :=
  HomologicalComplex.Hom.isoOfComponents f (by
    intro i j _
    apply (cancel_mono (b.f j)).mp
    simp only [Category.assoc]
    rw [← b.comm i j,← Category.assoc,hf,Category.assoc,E.hom.comm]
    rw [← Category.assoc,a.comm,Category.assoc,← hf])

end NSP14.Homological
