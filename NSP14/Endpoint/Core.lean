module
public import NSP14.Endpoint.Presentation
public import NSP14.Semigroup.AperyStandard
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

/-- The genuine degree/offset additive monoid. No numerical exponent
identifications are imposed here. -/
def corePoints : AddSubmonoid (ℕ×ℕ) :=
  AddSubmonoid.closure (Set.range (fun b : D.Variables => (1,b.val)))

def coreGeneratorPoint (b : D.Variables) : D.corePoints :=
  ⟨(1,b.val),AddSubmonoid.subset_closure ⟨b,rfl⟩⟩

theorem corePoint_mem {p : ℕ×ℕ} (hp : p∈D.corePoints) : p.1*D.m+p.2*D.d∈D.source := by
  apply AddSubmonoid.closure_induction (motive:=fun p _ => p.1*D.m+p.2*D.d∈D.source) ?_ ?_ ?_ hp
  · rintro p ⟨b,rfl⟩
    simpa only [one_mul] using D.source_generator b.val b.property
  · simpa only [Prod.fst_zero,Prod.snd_zero,zero_mul,zero_add] using D.source.zero_mem
  · intro p q _ _ hp hq
    convert D.source.add_mem hp hq using 1
    simp only [Prod.fst_add,Prod.snd_add]
    ring

def coreValue : D.corePoints →+ D.source.carrier where
  toFun p := ⟨p.val.1*D.m+p.val.2*D.d,D.corePoint_mem p.property⟩
  map_zero' := Subtype.ext (by simp)
  map_add' p q := Subtype.ext (by
    change (p.val.1+q.val.1)*D.m+(p.val.2+q.val.2)*D.d=
      (p.val.1*D.m+p.val.2*D.d)+(q.val.1*D.m+q.val.2*D.d)
    ring)

def coreDegree : D.corePoints →+ ℕ where
  toFun p := p.val.1
  map_zero' := rfl
  map_add' _ _ := rfl

def coreOffset : D.corePoints →+ ℕ where
  toFun p := p.val.2
  map_zero' := rfl
  map_add' _ _ := rfl

theorem corePoint_bound {p : ℕ×ℕ} (hp : p∈D.corePoints) : p.2≤D.u*p.1 := by
  apply AddSubmonoid.closure_induction (motive:=fun p _ => p.2≤D.u*p.1) ?_ ?_ ?_ hp
  · rintro p ⟨b,rfl⟩;simpa only [mul_one] using D.offset_le b.property
  · simp
  · intro p q _ _ hp hq
    change p.2+q.2≤D.u*(p.1+q.1)
    nlinarith

theorem corePoint_length {p : ℕ×ℕ} (hp : p∈D.corePoints) :
    D.source.HasLength (p.1*D.m+p.2*D.d) p.1 := by
  apply AddSubmonoid.closure_induction (motive:=fun p _ => D.source.HasLength (p.1*D.m+p.2*D.d) p.1) ?_ ?_ ?_ hp
  · rintro p ⟨b,rfl⟩
    simp only [one_mul]
    exact D.source.length_one (D.source_generator b.val b.property) (by have := D.m_pos;omega)
  · simpa only [Prod.fst_zero,Prod.snd_zero,zero_mul,zero_add] using D.source.length_zero
  · intro p q _ _ hp hq
    convert D.source.length_add hp hq using 1
    simp only [Prod.fst_add,Prod.snd_add]
    ring

theorem coreDegree_le_order (p : D.corePoints) : D.coreDegree p≤D.source.order (D.coreValue p).val :=
  D.source.length_le_order (D.corePoint_length p.property)

abbrev Core (k : Type*) [CommRing k] := AddMonoidAlgebra k D.corePoints

variable (k : Type) [Field k]
noncomputable def coreMonomial (p : D.corePoints) : D.Core k := AddMonoidAlgebra.single p (1:k)

/-- The actual degree-n class, including the case in which a longer
representation kills it. -/
noncomputable def coreInitial (p : D.corePoints) : D.source.TangentAlgebra k :=
  DirectSum.of (D.source.GradedPiece k) (D.coreDegree p)
    (D.source.monomialClass k _ (D.coreValue p) (D.coreDegree_le_order p))

theorem coreInitial_zero : D.coreInitial k 0=1 := by
  simp only [coreInitial,show D.coreValue 0=0 from (D.coreValue).map_zero]
  have h := D.source.initialMonomial_zero k
  unfold NumericalSemigroup.initialMonomial at h
  exact h

theorem coreInitial_add (p q : D.corePoints) : D.coreInitial k (p+q)=D.coreInitial k p*D.coreInitial k q := by
  simp only [coreInitial,map_add]
  rw [D.source.tangent_of_mul,D.source.gradedMul_monomial_layers]
  rfl

noncomputable def coreInitialHom : Multiplicative D.corePoints →* D.source.TangentAlgebra k where
  toFun p := D.coreInitial k p.toAdd
  map_one' := D.coreInitial_zero k
  map_mul' p q := D.coreInitial_add k p.toAdd q.toAdd

noncomputable def coreToG : D.Core k →ₐ[k] D.source.TangentAlgebra k :=
  AddMonoidAlgebra.lift k (D.source.TangentAlgebra k) D.corePoints (D.coreInitialHom k)

theorem coreToG_monomial (p : D.corePoints) : D.coreToG k (D.coreMonomial k p)=D.coreInitial k p := by
  change AddMonoidAlgebra.lift k (D.source.TangentAlgebra k) D.corePoints (D.coreInitialHom k) (AddMonoidAlgebra.single p (1:k))=_
  rw [AddMonoidAlgebra.lift_single,one_smul]
  rfl

theorem coreToG_monomial_zero_iff (p : D.corePoints) :
    D.coreToG k (D.coreMonomial k p)=0 ↔ D.coreDegree p<D.source.order (D.coreValue p).val := by
  rw [D.coreToG_monomial]
  unfold coreInitial
  rw [← map_zero (DirectSum.of (D.source.GradedPiece k) (D.coreDegree p)),
    (DirectSum.of_injective (β:=D.source.GradedPiece k) (D.coreDegree p)).eq_iff]
  exact D.source.monomialClass_eq_zero_iff k _ _ _
end NSP14.Endpoint.Data
