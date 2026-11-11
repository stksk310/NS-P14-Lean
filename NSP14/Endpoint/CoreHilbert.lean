module
public import NSP14.Endpoint.CoreLowDegrees
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

noncomputable def coreDegreeZeroEquiv : {p : D.CoreMinimalIndex // D.QCoreDegree p=0} ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := ⟨D.zeroMinimalIndex,rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    have he : (D.coreDegree p.val.val : ℤ)=0 := p.property
    have hn : D.coreDegree p.val.val=0 := by exact_mod_cast he
    exact ((D.core_degree_zero_iff p.val.val).mp hn).symm
  right_inv _ := rfl

variable (k : Type) [Field k]

theorem QCoreGrading_dimension (n : ℤ) : Module.finrank k ((D.QCoreGrading k).piece n)=
    Nat.card {p : D.CoreMinimalIndex // D.QCoreDegree p=n} := by
  change Module.finrank k ({p : D.CoreMinimalIndex // D.QCoreDegree p=n} →₀ k)=_
  rw [Module.finrank_finsupp_self,Nat.card_eq_fintype_card]

theorem QCoreGrading_zero_dim : Module.finrank k ((D.QCoreGrading k).piece 0)=1 := by
  rw [D.QCoreGrading_dimension,Nat.card_congr D.coreDegreeZeroEquiv]
  simp

theorem QCoreGrading_one_dim : Module.finrank k ((D.QCoreGrading k).piece 1)=D.q := by
  rw [D.QCoreGrading_dimension,←Nat.card_congr D.internalDegreeOneEquiv]
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe,q]

/-- The Hilbert function is attached to the actual standard grading. -/
noncomputable def coreHilbert (n : ℕ) : ℕ := Module.finrank k ((D.QCoreGrading k).piece n)

theorem coreHilbert_zero : D.coreHilbert k 0=1 := D.QCoreGrading_zero_dim k

theorem coreHilbert_one : D.coreHilbert k 1=D.q := D.QCoreGrading_one_dim k

theorem coreHilbert_above (n : ℕ) (hn : D.u≤n) : D.coreHilbert k n=0 := by
  have : Subsingleton ((D.QCoreGrading k).piece n) :=
    ModuleCat.subsingleton_of_isZero (D.QCoreGrading_above k n hn)
  exact Module.finrank_zero_of_subsingleton
end NSP14.Endpoint.Data
