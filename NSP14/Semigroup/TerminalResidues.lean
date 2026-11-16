module
public import NSP14.Semigroup.OffsetTelescoping
public import NSP14.Semigroup.ActualFinite
@[expose] public section
open scoped Classical BigOperators
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup)

noncomputable def residueAperyEquiv : Fin S.multiplicity ≃ S.AperyExponent :=
  Equiv.ofBijective (fun r => ⟨⟨S.apery r,S.apery_mem r⟩,(S.mem_aperySet_iff _).2 (S.apery_min r)⟩) (by
    constructor
    · intro r t he
      exact S.apery_injective (congrArg (fun a : S.AperyExponent => a.val.val) he)
    · intro a
      obtain ⟨r,_,hr⟩ := Finset.mem_image.mp a.property
      exact ⟨r,Subtype.ext (Subtype.ext hr)⟩)

noncomputable def residueTerminalEquiv :
    (Σ r : Fin S.multiplicity, ↥(S.residueTerminalIndices r)) ≃ S.TerminalExponent :=
  Equiv.ofBijective (fun a => ⟨⟨S.apery a.1 + a.2.val*S.multiplicity,S.apery_add_multiple _ _⟩,
    (S.mem_residueTerminalIndices _ _).1 a.2.property⟩) (by
    constructor
    · rintro ⟨r,p⟩ ⟨t,q⟩ he
      have hv := congrArg (fun a : S.TerminalExponent => a.val.val) he
      obtain ⟨hrt,hpq⟩ := S.decomposition_unique rfl hv
      change r=t at hrt
      change p.val=q.val at hpq
      subst t
      have heq : p=q := Subtype.ext hpq
      subst q
      rfl
    · intro a
      obtain ⟨q,hq⟩ := S.decomposition a.val.property
      have ht : S.Terminal (S.apery (S.residue a.val.val)+q*S.multiplicity) := hq ▸ a.property
      exact ⟨⟨S.residue a.val.val,⟨q,(S.mem_residueTerminalIndices _ _).2 ht⟩⟩,
        Subtype.ext (Subtype.ext hq.symm)⟩)

theorem terminal_excess_sum :
    (∑ a : S.TerminalExponent, (S.jump a.val.val-1)) =
      ∑ r : Fin S.multiplicity, (S.offsetLevel r-S.order (S.apery r)) := by
  rw [← S.residueTerminalEquiv.sum_comp]
  simp only [Fintype.sum_sigma, residueTerminalEquiv]
  apply Finset.sum_congr rfl
  intro r _
  rw [← S.terminal_residue_sum r]
  exact Finset.sum_coe_sort (S.residueTerminalIndices r) (fun q => S.jump (S.apery r+q*S.multiplicity)-1)

end NSP14.NumericalSemigroup
