module
public import NSP14.Lex.GenericDistractionProgress
public import NSP14.Lex.ElementaryDistraction
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Order.Prod.Lex.Basic
@[expose] public section
open scoped Classical BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem raisedExponent_degLex (α : Fin q →₀ ℕ) (a b : Fin q)
    (hab : a<b) (hb : 0<α b) :
    MonomialOrder.degLex.toSyn α<MonomialOrder.degLex.toSyn (raisedExponent q α a b) := by
  change toDegLex α<toDegLex (raisedExponent q α a b)
  rw [Finsupp.DegLex.lt_iff]
  exact Or.inr ⟨(raisedExponent_degree q α a b hb).symm,raisedExponent_lex q α a b hab⟩

/-- A maximal failure of an elementary raising move forces an actual strict prefix increase. -/
theorem genericMonomialStep_prefix_strict_of_maximal_raise
    (I : Ideal (MvPolynomial (Fin q) k)) (n : ℕ) (v : PolynomialDegreeIndex q n)
    (a b : Fin q) (hab : a<b) (m : ℕ) (hm : m<v.val b)
    (hv : MvPolynomial.monomial v.val (1:k)∈I)
    (hnot : MvPolynomial.monomial (raisedExponent q v.val a b) (1:k)∉I)
    (hmax : ∀ w : PolynomialDegreeIndex q n,
      MonomialOrder.degLex.toSyn v.val<MonomialOrder.degLex.toSyn w.val → m<w.val b →
      MvPolynomial.monomial w.val (1:k)∈I →
      MvPolynomial.monomial (raisedExponent q w.val a b) (1:k)∈I) :
    ∃ u : PolynomialDegreeIndex q n,
      monomialPrefixCard k q I n u<monomialPrefixCard (GenericDistractionField k q) q
        (genericMonomialStep k q I) n u := by
  have hb : 0<v.val b := by omega
  let u : PolynomialDegreeIndex q n := ⟨raisedExponent q v.val a b,
    (raisedExponent_degree q v.val a b hb).trans v.property⟩
  have hvu : MonomialOrder.degLex.toSyn v.val<MonomialOrder.degLex.toSyn u.val :=
    raisedExponent_degLex q v.val a b hab hb
  have hnotu : MvPolynomial.monomial u.val (1:k)∉I := hnot
  let S := MonomialPrefix k q I n u
  let rows : Option S ↪ PolynomialDegreeIndex q n := {
    toFun := fun j => match j with | none => u | some w => w.val
    inj' := by
      intro i j he
      cases i with
      | none =>
        cases j with
        | none => rfl
        | some w =>
          change u=w.val at he
          exact False.elim (hnotu (by simpa only [← he] using w.property.2))
      | some z =>
        cases j with
        | none =>
          change z.val=u at he
          exact False.elim (hnotu (by simpa only [he] using z.property.2))
        | some w => exact congrArg some (Subtype.ext he) }
  let cols : Option S ↪ PolynomialDegreeIndex q n := {
    toFun := fun j => match j with | none => v | some w => w.val
    inj' := by
      intro i j he
      cases i with
      | none =>
        cases j with
        | none => rfl
        | some w =>
          have hh := hvu.trans_le w.property.1
          exact False.elim ((ne_of_lt hh) (congrArg (fun x => MonomialOrder.degLex.toSyn x.val) he))
      | some z =>
        cases j with
        | none =>
          have hh := hvu.trans_le z.property.1
          exact False.elim ((ne_of_lt hh) (congrArg (fun x => MonomialOrder.degLex.toSyn x.val) he.symm))
        | some w => exact congrArg some (Subtype.ext he) }
  let key (j : Option S) := match j with
    | none => toLex (false,MonomialOrder.degLex.toSyn (0 : Fin q →₀ ℕ))
    | some w => toLex (true,MonomialOrder.degLex.toSyn w.val.val)
  have hkey : Function.Injective key := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some w => have hh := congrArg (fun z => (ofLex z).1) he; simp only [key] at hh; contradiction
    | some z =>
      cases j with
      | none => have hh := congrArg (fun z => (ofLex z).1) he; simp only [key] at hh; contradiction
      | some w =>
        have hh := congrArg (fun z => (ofLex z).2) he
        exact congrArg some (Subtype.ext (Subtype.ext (MonomialOrder.degLex.toSyn.injective hh)))
  let : LinearOrder (Option S) := LinearOrder.lift' key hkey
  let : LT (Option S) := (LinearOrder.lift' key hkey).toLT
  let : LE (Option S) := (LinearOrder.lift' key hkey).toLE
  let B := ((genericRawDegreeMatrix k q n).submatrix rows cols).map (elementaryParameterMap k q a b m)
  have hB (i j : Option S) : B i j=
      (if (cols j).val=(rows i).val then 1 else 0)+
      if m<(cols j).val b then if raisedExponent q (cols j).val a b=(rows i).val then 1 else 0 else 0 :=
    genericRawDegreeMatrix_elementary_entry k q a b m n (rows i) (cols j)
  have hdiag (j : Option S) : B j j=1 := by
    rw [hB]
    cases j with
    | none =>
      have hne : v.val≠u.val := fun h => (ne_of_lt hvu) (congrArg MonomialOrder.degLex.toSyn h)
      simp only [rows,cols,Function.Embedding.coeFn_mk,hne,ite_false,hm,ite_true,u,zero_add]
    | some w =>
      by_cases hmw : m<w.val.val b
      · have hraise := raisedExponent_degLex q w.val.val a b hab (by omega)
        have hne : raisedExponent q w.val.val a b≠w.val.val := fun h =>
          (ne_of_lt hraise) (congrArg MonomialOrder.degLex.toSyn h.symm)
        simp only [rows,cols,Function.Embedding.coeFn_mk,ite_true,hmw,hne,ite_false,add_zero]
      · simp only [rows,cols,Function.Embedding.coeFn_mk,ite_true,hmw,ite_false,add_zero]
  have htri : B.IsLowerTriangular := by
    intro i j hij
    rw [hB]
    cases i with
    | none =>
      cases j with
      | none => exact False.elim (lt_irrefl _ hij)
      | some w =>
        have hne : w.val.val≠u.val := fun h => hnotu (h ▸ w.property.2)
        by_cases hmw : m<w.val.val b
        · have hmem := hmax w.val (hvu.trans_le w.property.1) hmw w.property.2
          have hraise : raisedExponent q w.val.val a b≠u.val := fun h => hnotu (h ▸ hmem)
          simp only [rows,cols,Function.Embedding.coeFn_mk,hne,hraise,hmw,ite_false,ite_true,add_zero]
        · simp only [rows,cols,Function.Embedding.coeFn_mk,hne,hmw,ite_false,add_zero]
    | some z =>
      cases j with
      | none =>
        change key (some z)<key none at hij
        simp only [key,Prod.Lex.toLex_lt_toLex] at hij
        rcases hij with hij|⟨he,_⟩
        · exact False.elim ((by decide : ¬(true<false)) hij)
        · contradiction
      | some w =>
        have hzw : MonomialOrder.degLex.toSyn z.val.val<MonomialOrder.degLex.toSyn w.val.val := by
          change key (some z)<key (some w) at hij
          simpa only [key,Prod.Lex.toLex_lt_toLex,lt_self_iff_false,not_true_eq_false,false_or,true_and] using hij
        have hne : w.val.val≠z.val.val := fun h => (ne_of_lt hzw) (congrArg MonomialOrder.degLex.toSyn h.symm)
        by_cases hmw : m<w.val.val b
        · have hraise := raisedExponent_degLex q w.val.val a b hab (by omega)
          have hner : raisedExponent q w.val.val a b≠z.val.val := fun h =>
            (ne_of_lt (hzw.trans hraise)) (congrArg MonomialOrder.degLex.toSyn h.symm)
          simp only [rows,cols,Function.Embedding.coeFn_mk,hne,hner,hmw,ite_false,ite_true,add_zero]
        · simp only [rows,cols,Function.Embedding.coeFn_mk,hne,hmw,ite_false,add_zero]
  have hdetB : B.det≠0 := by
    rw [Matrix.det_of_isLowerTriangular B htri]
    simp only [hdiag,Finset.prod_const_one,ne_eq,one_ne_zero,not_false_eq_true]
  have hdet := genericFieldDegreeMatrix_minor_det_ne_zero_of_specialize k q n rows cols
    (elementaryParameterMap k q a b m) hdetB
  have hbound := genericMonomialStep_prefixCard_of_minor k q I n u rows cols
    (fun j => by cases j with | none => exact hv | some w => exact w.property.2)
    (fun j => by cases j with | none => exact le_rfl | some w => exact w.property.1) hdet
  refine ⟨u,?_⟩
  change Fintype.card S<_
  have hc : Fintype.card S+1≤monomialPrefixCard (GenericDistractionField k q) q
      (genericMonomialStep k q I) n u := by simpa only [Fintype.card_option] using hbound
  omega
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)

theorem genericMonomialStep_prefix_strict_of_raise
    (I : Ideal (MvPolynomial (Fin q) k)) (v : Fin q →₀ ℕ)
    (a b : Fin q) (hab : a<b) (hb : 0<v b)
    (hv : MvPolynomial.monomial v (1:k)∈I)
    (hnot : MvPolynomial.monomial (raisedExponent q v a b) (1:k)∉I) :
    ∃ (n : ℕ) (u : PolynomialDegreeIndex q n),
      monomialPrefixCard k q I n u<monomialPrefixCard (GenericDistractionField k q) q
        (genericMonomialStep k q I) n u := by
  let m := v b-1
  let n := v.degree
  let bad := Finset.univ.filter (fun w : PolynomialDegreeIndex q n =>
    m<w.val b ∧ MvPolynomial.monomial w.val (1:k)∈I ∧
      MvPolynomial.monomial (raisedExponent q w.val a b) (1:k)∉I)
  let key (w : PolynomialDegreeIndex q n) := MonomialOrder.degLex.toSyn w.val
  let D := bad.image key
  have hvbad : (⟨v,rfl⟩ : PolynomialDegreeIndex q n)∈bad := by
    simp only [bad,Finset.mem_filter,Finset.mem_univ,true_and]
    exact ⟨by dsimp only [m]; omega,hv,hnot⟩
  have hD : D.Nonempty := ⟨key ⟨v,rfl⟩,Finset.mem_image.mpr ⟨⟨v,rfl⟩,hvbad,rfl⟩⟩
  obtain ⟨w,hw,he⟩ := Finset.mem_image.mp (Finset.max'_mem D hD)
  have hwb : m<w.val b ∧ MvPolynomial.monomial w.val (1:k)∈I ∧
      MvPolynomial.monomial (raisedExponent q w.val a b) (1:k)∉I := by
    simpa only [bad,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hmax (z : PolynomialDegreeIndex q n)
      (hwz : MonomialOrder.degLex.toSyn w.val<MonomialOrder.degLex.toSyn z.val)
      (hmz : m<z.val b) (hz : MvPolynomial.monomial z.val (1:k)∈I) :
      MvPolynomial.monomial (raisedExponent q z.val a b) (1:k)∈I := by
    by_contra hzn
    have hzbad : z∈bad := by
      simp only [bad,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨hmz,hz,hzn⟩
    have hle := Finset.le_max' D (key z) (Finset.mem_image.mpr ⟨z,hzbad,rfl⟩)
    rw [← he] at hle
    exact not_lt_of_ge hle hwz
  obtain ⟨u,hu⟩ := genericMonomialStep_prefix_strict_of_maximal_raise k q I n w a b hab m
    hwb.1 hwb.2.1 hwb.2.2 hmax
  exact ⟨n,u,hu⟩

def IsStronglyStable (I : Ideal (MvPolynomial (Fin q) k)) : Prop :=
  IsMonomial k q I ∧ ∀ v,MvPolynomial.monomial v (1:k)∈I →
    ∀ a b,0<v b → a<b → MvPolynomial.monomial (raisedExponent q v a b) (1:k)∈I

/-- A genuine fixed support of the generic operation is strongly stable in every characteristic.
This does not identify it as lexicographic. -/
theorem genericMonomialStep_fixed_stronglyStable (I : Ideal (MvPolynomial (Fin q) k))
    (hmono : IsMonomial k q I)
    (hfix : ∀ v,MvPolynomial.monomial v (1:GenericDistractionField k q)∈genericMonomialStep k q I ↔
      MvPolynomial.monomial v (1:k)∈I) : IsStronglyStable k q I := by
  refine ⟨hmono,?_⟩
  intro v hv a b hb hab
  by_contra hn
  obtain ⟨n,u,hu⟩ := genericMonomialStep_prefix_strict_of_raise k q I v a b hab hb hv hn
  simp only [monomialPrefixCard,MonomialPrefix,hfix] at hu
  exact lt_irrefl _ hu
end NSP14.Lex

namespace NSP14.Lex
variable (k : Type) [Field k] (q : ℕ)
theorem genericMonomialStep_fixed_raise (I : Ideal (MvPolynomial (Fin q) k))
    (hmono : IsMonomial k q I)
    (hfix : ∀ v,MvPolynomial.monomial v (1:GenericDistractionField k q)∈genericMonomialStep k q I ↔
      MvPolynomial.monomial v (1:k)∈I)
    (v : Fin q →₀ ℕ) (hv : MvPolynomial.monomial v (1:k)∈I)
    (a b : Fin q) (hb : 0<v b) (hab : a<b) :
    MvPolynomial.monomial (raisedExponent q v a b) (1:k)∈I :=
  (genericMonomialStep_fixed_stronglyStable k q I hmono hfix).2 v hv a b hb hab
end NSP14.Lex
