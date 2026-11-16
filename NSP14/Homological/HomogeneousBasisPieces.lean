module
public import NSP14.Homological.GradedBasis
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Homological
variable (k σ : Type) [Field k] {J : Type}
  (M : ModuleCat (VariableRing k σ)) (G : GradedPolynomialModule k σ M)
  (b : Module.Basis J k (coefficientModule k σ M)) (deg : J → ℤ)
  (hb : ∀ a,b a ∈ G.degreeSpace (deg a))

include hb in
theorem homogeneous_basis_span (q : ℤ) :
    Submodule.span k (Set.range (fun a : {a : J //deg a=q} => b a.val))=G.degreeSpace q := by
  rw [gradedBasis_degreeSpace_eq_span k σ M G b deg hb]
  congr 1
  ext a
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,i.property,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,rfl⟩

/-- Restrict a genuine homogeneous basis to one actual degree. The whole
module may be infinite-dimensional over the field. -/
noncomputable def homogeneousPieceBasis (q : ℤ) : Module.Basis {a : J //deg a=q} k (G.piece q) :=
  ((Module.Basis.span (b.linearIndependent.comp
      (Subtype.val : {a : J //deg a=q} → J) Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (homogeneous_basis_span k σ M G b deg hb q))).map (G.rangeEquiv q).symm

include hb in
theorem homogeneousPieceBasis_inclusion (q : ℤ) (a : {a : J //deg a=q}) :
    G.inclusion q (homogeneousPieceBasis k σ M G b deg hb q a)=b a.val := by
  unfold homogeneousPieceBasis
  simp only [Module.Basis.map_apply]
  let z : G.degreeSpace q := (LinearEquiv.ofEq _ _ (homogeneous_basis_span k σ M G b deg hb q))
    ((Module.Basis.span (b.linearIndependent.comp
      (Subtype.val : {a : J //deg a=q} → J) Subtype.val_injective)) a)
  have he := congrArg Subtype.val ((G.rangeEquiv q).apply_symm_apply z)
  change G.inclusion q ((G.rangeEquiv q).symm z)=z.val at he
  have hz : z.val=b a.val := by
    exact Module.Basis.coe_span_apply _ a
  change G.inclusion q ((G.rangeEquiv q).symm z)=b a.val
  exact he.trans hz

include hb in
theorem homogeneous_piece_finite (q : ℤ) [Finite {a : J //deg a=q}] : Module.Finite k (G.piece q) := by
  let : Fintype {a : J //deg a=q} := Fintype.ofFinite _
  exact Module.Finite.of_basis (homogeneousPieceBasis k σ M G b deg hb q)

include hb in
theorem homogeneous_piece_finrank (q : ℤ) [Finite {a : J //deg a=q}] :
    Module.finrank k (G.piece q)=Nat.card {a : J //deg a=q} := by
  let : Fintype {a : J //deg a=q} := Fintype.ofFinite _
  rw [Module.finrank_eq_card_basis (homogeneousPieceBasis k σ M G b deg hb q),Nat.card_eq_fintype_card]
end NSP14.Homological
