module
public import NSP14.Semigroup.AperyQuotient
public import NSP14.Semigroup.AlgebraPresentation
@[expose] public section
open scoped Classical
namespace NSP14.NumericalSemigroup
variable (S : NumericalSemigroup) (k : Type) [Field k]

noncomputable def semigroupX : S.SemigroupRing k :=
  AddMonoidAlgebra.single S.multiplicityExponent 1

noncomputable def semigroupXIdeal : Ideal (S.SemigroupRing k) :=
  Ideal.span {S.semigroupX k}

theorem semigroupX_regular : Function.Injective (fun a : S.SemigroupRing k => S.semigroupX k*a) := by
  intro a b h
  apply AddMonoidAlgebra.ext
  apply Finsupp.ext
  intro y
  have he := congrArg (fun f : S.SemigroupRing k => f.coeff (S.multiplicityExponent+y)) h
  simpa only [semigroupX,AddMonoidAlgebra.coeff_single_mul_add,one_mul] using he

theorem mem_semigroupXIdeal (a : S.SemigroupRing k) :
    a ∈ S.semigroupXIdeal k ↔ ∀ x : S.AperyExponent,a.coeff x.val=0 := by
  have hs : S.semigroupXIdeal k=Ideal.span
      (AddMonoidAlgebra.of' k S.carrier '' ({S.multiplicityExponent} : Set S.carrier)) := by
    simp only [Set.image_singleton]
    rfl
  rw [hs,AddMonoidAlgebra.mem_ideal_span_of'_image]
  constructor
  · intro h x
    by_contra hn
    obtain ⟨z,hz,y,he⟩ := h x.val (Finsupp.mem_support_iff.mpr hn)
    have hz' : z=S.multiplicityExponent := Set.mem_singleton_iff.mp hz
    subst z
    exact S.apery_no_predecessor x.property ⟨y.val,y.property,congrArg Subtype.val he⟩
  · intro h x hx
    have hn : x.val ∉ S.aperySet := by
      intro ha
      exact Finsupp.mem_support_iff.mp hx (h ⟨x,ha⟩)
    have hp : ∃ y ∈ S,x.val=y+S.multiplicity := by
      by_contra hno
      exact hn ((S.mem_apery_iff_no_predecessor x.property).mpr hno)
    obtain ⟨y,hy,he⟩ := hp
    exact ⟨S.multiplicityExponent,Set.mem_singleton _,⟨y,hy⟩,Subtype.ext he⟩
end NSP14.NumericalSemigroup
