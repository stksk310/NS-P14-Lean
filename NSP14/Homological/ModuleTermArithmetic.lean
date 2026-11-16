module
public import NSP14.Homological.InitialModule
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.Homological
variable {σ : Type*} (m : MonomialOrder σ) {q : ℕ}

noncomputable def moduleTermExponent (i : ModuleTerm m (q:=q)) : σ →₀ ℕ := m.toSyn.symm (ofLex i).1

theorem moduleTerm_ext {i j : ModuleTerm m (q:=q)}
    (he : moduleTermExponent m i=moduleTermExponent m j) (hl : (ofLex i).2=(ofLex j).2) : i=j := by
  apply ofLex.injective
  exact Prod.ext (m.toSyn.symm.injective he) hl

theorem moduleTermExponent_shift (d : σ →₀ ℕ) (i : ModuleTerm m (q:=q)) :
    moduleTermExponent m (moduleTermShift m d i)=moduleTermExponent m i+d := by
  simp only [moduleTermExponent,moduleTermShift,ofLex_toLex,map_add,AddEquiv.symm_apply_apply]

theorem moduleTermShift_add (d e : σ →₀ ℕ) (i : ModuleTerm m (q:=q)) :
    moduleTermShift m d (moduleTermShift m e i)=moduleTermShift m (d+e) i := by
  apply moduleTerm_ext
  · simp only [moduleTermExponent_shift,add_comm,add_assoc]
  · rfl

noncomputable def moduleTermDivide (v : σ) (i : ModuleTerm m (q:=q)) : ModuleTerm m (q:=q) :=
  toLex (m.toSyn (moduleTermExponent m i-Finsupp.single v 1),(ofLex i).2)

theorem moduleTermShift_divide (v : σ) (i : ModuleTerm m (q:=q)) (hv : 0 < moduleTermExponent m i v) :
    moduleTermShift m (Finsupp.single v 1) (moduleTermDivide m v i)=i := by
  have hd : Finsupp.single v 1 ≤ moduleTermExponent m i := by
    intro w
    by_cases hw : v=w
    · subst w
      simpa only [Finsupp.single_eq_same] using (Nat.succ_le_of_lt hv)
    · simp only [Finsupp.single_eq_of_ne (Ne.symm hw),zero_le]
  apply moduleTerm_ext
  · rw [moduleTermExponent_shift]
    change m.toSyn.symm (m.toSyn (moduleTermExponent m i-Finsupp.single v 1)) +
      Finsupp.single v 1 = moduleTermExponent m i
    rw [AddEquiv.symm_apply_apply]
    exact tsub_add_cancel_of_le hd
  · rfl

variable (k : Type*) [Field k] {M : Type*} [AddCommGroup M] [Module k M]
  [Module (MvPolynomial σ k) M] [IsScalarTower k (MvPolynomial σ k) M]
  (g : Fin q → M)

theorem moduleStandard_divide_mem (v : σ) (i : ModuleStandard k m g)
    (hv : 0 < moduleTermExponent m i.val v) : moduleTermDivide m v i.val ∈ ModuleStandard k m g := by
  apply moduleStandard_divisor k m g (Finsupp.single v 1) (moduleTermDivide m v i.val)
  rw [moduleTermShift_divide m v i.val hv]
  exact i.property

noncomputable def moduleStandardDivide (v : σ) (i : ModuleStandard k m g)
    (hv : 0 < moduleTermExponent m i.val v) : ModuleStandard k m g :=
  ⟨moduleTermDivide m v i.val,moduleStandard_divide_mem m k g v i hv⟩
end NSP14.Homological
