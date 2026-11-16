module
public import NSP14.ArithmeticSequence.Order
public import NSP14.Semigroup.KernelHead
@[expose] public section
namespace NSP14.ArithmeticSequence.Data
variable (D : NSP14.ArithmeticSequence.Data)

theorem not_terminal (x : ℕ) : ¬D.source.Terminal x := by
  intro hx
  have h := D.order_add_m hx.1
  rw [← D.multiplicity] at h
  have ht := hx.2
  omega

theorem head_iff_apery (x : ℕ) : D.source.XHead x ↔ x ∈ D.source.aperySet := by
  constructor
  · intro hx
    apply (D.source.mem_apery_iff_no_predecessor hx.1).mpr
    rintro ⟨y,hy,he⟩
    exact hx.2 ⟨y,hy,he,by rw [he,D.multiplicity,D.order_add_m hy]⟩
  · intro hx
    refine ⟨((D.source.mem_aperySet_iff _).mp hx).1,?_⟩
    rintro ⟨y,hy,he,_⟩
    exact D.source.apery_no_predecessor hx ⟨y,hy,he⟩

variable (k : Type*) [CommRing k] [Nontrivial k]

/-- x is regular on the actual algebraic AP tangent cone, for every d and
in every characteristic. The proof controls all linear combinations via the
actual kernel coordinates, not only individual monomials. -/
theorem xMultiply_injective : Function.Injective (D.source.xMultiply k) := by
  have : IsEmpty D.source.TerminalExponent := ⟨fun x => D.not_terminal x.val.val x.property⟩
  have : Subsingleton (D.source.TerminalExponent →₀ k) := inferInstance
  have : Subsingleton (D.source.xMultiply k).ker :=
    (D.source.xKernelEquiv k).injective.subsingleton
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro a ha
  change a=0
  have h : (⟨a,ha⟩ : (D.source.xMultiply k).ker)=0 := Subsingleton.elim _ _
  exact congrArg Subtype.val h
end NSP14.ArithmeticSequence.Data
