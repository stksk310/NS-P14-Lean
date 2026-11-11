module
public import NSP14.Endpoint.TwoScalarSocle
public import NSP14.Endpoint.CoreHilbert
public import NSP14.Endpoint.CoreAugmentation
public import NSP14.Endpoint.FullTransfer
public import NSP14.Homological.FiniteKoszulEulerAbove
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
namespace NSP14.Endpoint.Data
variable (D : NSP14.Endpoint.Data)

noncomputable def twoInternalEquiv (hq : D.q=2) : D.a ≃ Fin 2 :=
  Fintype.equivFinOfCardEq (by rw [Fintype.card_coe];exact hq)

noncomputable def twoInternalList (hq : D.q=2) : List D.a :=
  [(D.twoInternalEquiv hq).symm 1,(D.twoInternalEquiv hq).symm 0]

theorem twoInternalList_mem (hq : D.q=2) (b : D.a) : b∈D.twoInternalList hq := by
  have he : D.twoInternalEquiv hq b=0 ∨ D.twoInternalEquiv hq b=1 := by
    have hi := (D.twoInternalEquiv hq b).isLt
    by_cases h : (D.twoInternalEquiv hq b).val=0
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by omega))
  rcases he with he|he
  · have hb : b=(D.twoInternalEquiv hq).symm 0 := (D.twoInternalEquiv hq).eq_symm_apply.mpr he
    simp [twoInternalList,hb]
  · have hb : b=(D.twoInternalEquiv hq).symm 1 := (D.twoInternalEquiv hq).eq_symm_apply.mpr he
    simp [twoInternalList,hb]

theorem twoInternalList_nodup (hq : D.q=2) : (D.twoInternalList hq).Nodup := by
  simp [twoInternalList]

variable (k : Type) [Field k]

noncomputable def internalSocle (hq : D.q=2) : Submodule k (D.QCore k) :=
  NSP14.Endpoint.twoScalarSocle k (D.QCore k)
    (D.internalToQCore k (MvPolynomial.X ((D.twoInternalEquiv hq).symm 0)))
    (D.internalToQCore k (MvPolynomial.X ((D.twoInternalEquiv hq).symm 1)))

noncomputable def internalSigma (hq : D.q=2) : ℕ := Module.finrank k (D.internalSocle k hq)

/-- Internal socle sigma_C is the actual annihilator in QC and is
separate from the endpoint socle R in G. -/
noncomputable def QCoreTwoSocleEquiv (hq : D.q=2) :
    koszulHomologyK k D.a (D.QCoreModule k) 2 ≃ₗ[k] D.internalSocle k hq :=
  (fullListHomologyKIso k D.a (D.twoInternalList hq) (D.twoInternalList_mem hq)
    (D.twoInternalList_nodup hq) (D.QCoreModule k) 2).toLinearEquiv.trans
      (((coefficientComplexHomologyIso k (regularPartialPolynomialIso k (D.QCore k) D.a
        (D.internalToQCore k) (D.twoInternalList hq)) 2).symm.toLinearEquiv).trans
          (NSP14.Endpoint.twoScalarH2Equiv k (D.QCore k)
            (D.internalToQCore k (MvPolynomial.X ((D.twoInternalEquiv hq).symm 0)))
            (D.internalToQCore k (MvPolynomial.X ((D.twoInternalEquiv hq).symm 1)))))

theorem QCore_two_betti_two (hq : D.q=2) : totalBetti k D.a (D.QCoreModule k) 2=D.internalSigma k hq :=
  (D.QCoreTwoSocleEquiv k hq).finrank_eq

theorem QCore_two_betti_one (hq : D.q=2) : totalBetti k D.a (D.QCoreModule k) 1=D.internalSigma k hq+1 := by
  have h := finite_koszul_bettiEuler_top k D.a (D.QCoreModule k) (by rw [Fintype.card_coe];have := D.q_two;omega)
  rw [Fintype.card_coe,show D.a.card=2 from hq,bettiEuler_succ,bettiEuler_succ,bettiEuler_zero,
    D.QCore_betti_zero,D.QCore_two_betti_two k hq] at h
  change (D.internalSigma k hq : ℤ)-((totalBetti k D.a (D.QCoreModule k) 1 : ℤ)-1)=0 at h
  omega

theorem QCore_two_betti_above (hq : D.q=2) (i : ℕ) (hi : 2 < i) : totalBetti k D.a (D.QCoreModule k) i=0 :=
  totalBetti_eq_zero_of_gt k D.a _ i (by rw [Fintype.card_coe];change D.q < i;rw [hq];exact hi)
end NSP14.Endpoint.Data
