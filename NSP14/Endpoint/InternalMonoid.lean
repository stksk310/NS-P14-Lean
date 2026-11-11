module
public import NSP14.Endpoint.TwoRows
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Endpoint.Data
variable (D : Data)

def internalPoint : (D.a →₀ ℕ) →+ D.corePoints where
  toFun β := ∑ b : D.a,β b • D.coreGeneratorPoint (D.internalVariable b)
  map_zero' := by simp
  map_add' β γ := by simp only [Finsupp.add_apply,add_nsmul,Finset.sum_add_distrib]

theorem internalPoint_single (b : D.a) : D.internalPoint (Finsupp.single b 1)=
    D.coreGeneratorPoint (D.internalVariable b) := by
  simp [internalPoint,Finsupp.single_apply]

theorem internalPoint_degree (β : D.a →₀ ℕ) : D.coreDegree (D.internalPoint β)=∑ b : D.a,β b := by
  change D.coreDegree (∑ b : D.a,β b • D.coreGeneratorPoint (D.internalVariable b))=_
  simp only [map_sum,map_nsmul]
  simp only [show ∀ b : D.a,D.coreDegree (D.coreGeneratorPoint (D.internalVariable b))=1 from fun _ => rfl,
    smul_eq_mul,mul_one]

theorem internalPoint_offset (β : D.a →₀ ℕ) : D.coreOffset (D.internalPoint β)=∑ b : D.a,β b*b.val := by
  change D.coreOffset (∑ b : D.a,β b • D.coreGeneratorPoint (D.internalVariable b))=_
  simp only [map_sum,map_nsmul]
  rfl

theorem twoInternal_sum (hq : D.q=2) (f : D.a → ℕ) :
    ∑ b : D.a,f b=f ((D.twoInternalEquiv hq).symm 0)+f ((D.twoInternalEquiv hq).symm 1) := by
  rw [←(D.twoInternalEquiv hq).symm.sum_comp f]
  exact Fin.sum_univ_two _

theorem internalPoint_injective_two (hq : D.q=2) : Function.Injective D.internalPoint := by
  intro β γ h
  let a := (D.twoInternalEquiv hq).symm 0
  let b := (D.twoInternalEquiv hq).symm 1
  have hn := congrArg D.coreDegree h
  have hB := congrArg D.coreOffset h
  rw [D.internalPoint_degree,D.internalPoint_degree,D.twoInternal_sum hq,D.twoInternal_sum hq] at hn
  rw [D.internalPoint_offset,D.internalPoint_offset,D.twoInternal_sum hq,D.twoInternal_sum hq] at hB
  change β a+β b=γ a+γ b at hn
  change β a*a.val+β b*b.val=γ a*a.val+γ b*b.val at hB
  have hab : a.val≠b.val := by
    intro he
    have hs : a=b := Subtype.ext he
    have hh := (D.twoInternalEquiv hq).symm.injective hs
    exact (by decide : (0:Fin 2)≠1) hh
  have he : (a.val:ℤ)-(b.val:ℤ)≠0 := by omega
  have hm : ((a.val:ℤ)-(b.val:ℤ))*((β a:ℤ)-(γ a:ℤ))=0 := by
    have hn' : (β a:ℤ)+β b=γ a+γ b := by exact_mod_cast hn
    have hB' : (β a:ℤ)*a.val+β b*b.val=γ a*a.val+γ b*b.val := by exact_mod_cast hB
    nlinarith
  have ha : β a=γ a := by have := (mul_eq_zero.mp hm).resolve_left he;omega
  have hb : β b=γ b := by omega
  ext x
  have hx := D.twoInternalList_mem hq x
  have hx' : x=b ∨ x=a := by simpa only [twoInternalList,List.mem_cons,List.not_mem_nil,or_false] using hx
  rcases hx' with rfl|rfl
  · exact hb
  · exact ha

variable (k : Type) [Field k]

theorem internalToCore_mapDomain : D.internalToCore k=AddMonoidAlgebra.mapDomainAlgHom k k D.internalPoint := by
  apply MvPolynomial.algHom_ext
  intro b
  rw [D.internalToCore_X]
  change D.coreMonomial k (D.coreGeneratorPoint (D.internalVariable b))=
    AddMonoidAlgebra.mapDomain D.internalPoint (AddMonoidAlgebra.single (Finsupp.single b 1) 1)
  rw [AddMonoidAlgebra.mapDomain_single,D.internalPoint_single]
  rfl
end NSP14.Endpoint.Data
