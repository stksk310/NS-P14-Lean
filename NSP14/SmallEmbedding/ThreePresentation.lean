module
public import NSP14.SmallEmbedding.Base
public import NSP14.Endpoint.NativeTransfer
public import NSP14.Endpoint.SocleBounds
public import NSP14.Endpoint.CoreAugmentation
public import NSP14.Width.EdgeAP
@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 4096
open scoped Classical BigOperators
open NSP14.Endpoint CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological

/-! Positive-alphabet version of the existing actual endpoint construction.
The original Endpoint.Data API remains byte-for-byte unchanged. Its old lower bound
on alphabet cardinality is used only to prove nonemptiness in these common modules.
Every proof below is replayed for the positive-alphabet structure, with no new
Tor/resource/comparison premise. The one-letter specialization is consumed in LanTuVu.
Source correspondence and hashes: verification/run19/sources/three-positive-endpoint-port_20261116.json.
-/

-- Replayed common endpoint module: NSP14.Endpoint.Data; source SHA256 2a3b13d265a54a68ba7234933fe9b97214bdfdae973a50eb4ad04c4368f04547.
open scoped Classical
namespace NSP14.SmallEmbedding

/-- The broad endpoint hypotheses. In particular no bound d*u<m,
no gcd(m,u)=1 and no Cohen--Macaulay hypothesis is present. -/
structure ThreeData where
  m : ℕ
  d : ℕ
  u : ℕ
  a : Finset ℕ
  q_one : 1 ≤ a.card
  a_pos : ∀ b∈a,0 < b
  a_lt : ∀ b∈a,b < u
  u_lt : u < m
  d_pos : 1 ≤ d
  offsets_coprime : Nat.gcd (a.gcd id) u=1
  coprime : Nat.Coprime m d

namespace ThreeData
variable (D : ThreeData)
def q : ℕ := D.a.card

def offsets : Finset ℕ := insert 0 (insert D.u D.a)
def generators : Finset ℕ := D.offsets.image (fun b => D.m+b*D.d)

@[simp] theorem mem_offsets (b : ℕ) : b∈D.offsets ↔ b=0 ∨ b=D.u ∨ b∈D.a := by
  simp only [offsets,Finset.mem_insert]

theorem u_pos : 0 < D.u := by
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < D.a.card by have := D.q_one;omega)
  have := D.a_pos b hb
  have := D.a_lt b hb
  omega

theorem m_pos : 0 < D.m := D.u_pos.trans D.u_lt

theorem offset_le {b : ℕ} (hb : b∈D.offsets) : b≤D.u := by
  rcases (D.mem_offsets b).mp hb with rfl|rfl|hb
  · omega
  · rfl
  · exact (D.a_lt b hb).le

theorem offsets_card : D.offsets.card=D.q+2 := by
  have h0 : 0∉D.a := fun h => Nat.lt_irrefl 0 (D.a_pos 0 h)
  have hu : D.u∉D.a := fun h => Nat.lt_irrefl D.u (D.a_lt D.u h)
  rw [offsets,Finset.card_insert_of_notMem (by simpa only [Finset.mem_insert,not_or] using And.intro (Nat.ne_of_lt D.u_pos) h0),Finset.card_insert_of_notMem hu]
  rfl

theorem generator_injective : Function.Injective (fun b : ℕ => D.m+b*D.d) := by
  intro a b h
  have := D.d_pos
  nlinarith

theorem generator_mem (b : ℕ) (hb : b∈D.offsets) : D.m+b*D.d∈D.generators :=
  Finset.mem_image.mpr ⟨b,hb,rfl⟩

theorem generators_setGcd : Nat.setGcd (D.generators : Set ℕ)=1 := by
  let g := Nat.setGcd (D.generators : Set ℕ)
  have hm : g∣D.m := by
    simpa only [Nat.zero_mul,Nat.add_zero] using
      (Nat.setGcd_dvd_of_mem (D.generator_mem 0 (by simp)))
  have hc : Nat.Coprime g D.d := Nat.Coprime.of_dvd_left hm D.coprime
  have hoff (b : ℕ) (hb : b∈D.offsets) : g∣b := by
    have h := Nat.setGcd_dvd_of_mem (D.generator_mem b hb)
    have hd : g∣b*D.d := (Nat.dvd_add_iff_right hm).mpr h
    exact hc.dvd_of_dvd_mul_right hd
  apply Nat.dvd_one.mp
  rw [← D.offsets_coprime]
  exact Nat.dvd_gcd (Finset.dvd_gcd (fun b hb => hoff b (by simp [hb]))) (hoff D.u (by simp))

theorem cofinite_closure : ∃ c,∀ n,c≤n → n∈AddSubmonoid.closure (D.generators : Set ℕ) := by
  obtain ⟨c,hc⟩ := Nat.exists_mem_closure_of_ge (D.generators : Set ℕ)
  exact ⟨c,fun n hn => hc n hn (by rw [D.generators_setGcd];exact one_dvd _)⟩

noncomputable def source : NumericalSemigroup where
  carrier := AddSubmonoid.closure (D.generators : Set ℕ)
  conductor := Nat.find D.cofinite_closure
  cofinite := Nat.find_spec D.cofinite_closure

theorem source_generator (b : ℕ) (hb : b∈D.offsets) : D.m+b*D.d∈D.source :=
  AddSubmonoid.subset_closure (D.generator_mem b hb)

/-- Every actual representation has its real length and nonnegative
offset sum, before any endpoint-coordinate reduction. -/
theorem representation {x : ℕ} (hx : x∈D.source) :
    ∃ n B : ℕ,B≤D.u*n ∧ x=n*D.m+B*D.d := by
  apply AddSubmonoid.closure_induction (motive:=fun x _ => ∃ n B : ℕ,B≤D.u*n ∧ x=n*D.m+B*D.d) ?_ ?_ ?_ hx
  · intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact ⟨1,b,by simpa only [Nat.mul_one] using D.offset_le hb,by simp⟩
  · exact ⟨0,0,by simp,by simp⟩
  · rintro x y _ _ ⟨n,B,hB,rfl⟩ ⟨l,C,hC,rfl⟩
    exact ⟨n+l,B+C,by nlinarith,by ring⟩

theorem representation_length_pos {x n B : ℕ} (hx : 0 < x) (hB : B≤D.u*n)
    (he : x=n*D.m+B*D.d) : 1≤n := by
  by_contra hn
  have hn0 : n=0 := by omega
  have hB0 : B=0 := by simp only [hn0,Nat.mul_zero] at hB;omega
  simp only [hn0,hB0,Nat.zero_mul,Nat.zero_add] at he
  omega

theorem multiplicity : D.source.multiplicity=D.m := by
  apply D.source.multiplicity_eq D.m_pos (by simpa using D.source_generator 0 (by simp))
  intro x hx hp
  obtain ⟨n,B,hB,he⟩ := D.representation hx
  have hn := D.representation_length_pos hp hB he
  have hm := Nat.mul_le_mul_right D.m hn
  nlinarith

theorem generator_atom (b : ℕ) (hb : b∈D.offsets) : D.source.IsAtom (D.m+b*D.d) := by
  refine ⟨D.source_generator b hb,by have := D.m_pos;omega,?_⟩
  intro x hx y hy he
  by_cases hx0 : x=0
  · exact Or.inl hx0
  by_cases hy0 : y=0
  · exact Or.inr hy0
  exfalso
  obtain ⟨n,B,hB,hx⟩ := D.representation hx
  obtain ⟨l,C,hC,hy⟩ := D.representation hy
  have hn := D.representation_length_pos (by omega : 0 < x) hB hx
  have hl := D.representation_length_pos (by omega : 0 < y) hC hy
  have heq : D.m+b*D.d=(n+l)*D.m+(B+C)*D.d := by rw [he,hx,hy];ring
  have hbc : B+C≤b := by
    have h := Nat.mul_le_mul_right D.m (show 1≤n+l by omega)
    have := D.d_pos
    nlinarith
  have hmod : b*D.d ≡ (B+C)*D.d [MOD D.m] := by
    have h := congrArg (fun a => a%D.m) heq
    change (b*D.d)%D.m=((B+C)*D.d)%D.m
    simpa only [Nat.add_mod,Nat.mod_self,Nat.mul_mod_left,Nat.zero_add,Nat.mod_mod] using h
  have hc := hmod.cancel_right_of_coprime D.coprime.gcd_eq_one
  have hb' : b < D.m := (D.offset_le hb).trans_lt D.u_lt
  have hbc' : B+C < D.m := hbc.trans_lt hb'
  have hh : b=B+C := by
    change b%D.m=(B+C)%D.m at hc
    simpa only [Nat.mod_eq_of_lt hb',Nat.mod_eq_of_lt hbc'] using hc
  have hmul := Nat.mul_le_mul_right D.m (show 2≤n+l by omega)
  have := D.m_pos
  rw [hh] at heq
  omega

theorem atoms : D.source.atoms=D.generators := by
  ext x
  rw [D.source.mem_atoms_iff]
  constructor
  · intro hx
    exact D.source.atom_mem_of_generates rfl hx
  · intro hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact D.generator_atom b hb

theorem embeddingDimension : D.source.embeddingDimension=D.q+2 := by
  unfold NumericalSemigroup.embeddingDimension
  rw [D.atoms,generators,Finset.card_image_of_injective _ D.generator_injective,D.offsets_card]

theorem maxAtom : D.source.maxAtom=D.m+D.u*D.d := by
  apply Nat.le_antisymm
  · have hh : D.source.maxAtom∈D.generators := by
      rw [← D.atoms]
      exact Finset.max'_mem _ _
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hh
    rw [← he]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right D.d (D.offset_le hb)) D.m
  · exact D.source.atom_le_maxAtom (D.atoms ▸ D.generator_mem D.u (by simp))

theorem width : D.source.width=D.d*D.u := by
  unfold NumericalSemigroup.width
  rw [D.maxAtom,D.multiplicity,Nat.add_sub_cancel_left,Nat.mul_comm]
end ThreeData
end NSP14.SmallEmbedding


-- Replayed common endpoint module: NSP14.Endpoint.Presentation; source SHA256 b872cf60ec7cfca61c28e5bd7dcd714e8b834bc2677ad89593e21e823af0eaec.
open scoped Classical
open NSP14.Homological CategoryTheory
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

abbrev Variables := ↥D.offsets

noncomputable def atomVariable (b : D.Variables) : D.source.AtomExponent :=
  ⟨⟨D.m+b.val*D.d,D.source_generator b.val b.property⟩,D.generator_atom b.val b.property⟩

noncomputable def atomVariableEquiv : D.Variables ≃ D.source.AtomExponent :=
  Equiv.ofBijective D.atomVariable ⟨by
    intro a b h
    apply Subtype.ext
    exact D.generator_injective (congrArg (fun x : D.source.AtomExponent => x.val.val) h),by
    intro x
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp (D.atoms ▸ (D.source.mem_atoms_iff _).mpr x.property)
    exact ⟨⟨b,hb⟩,Subtype.ext (Subtype.ext he)⟩⟩

theorem variables_card : Fintype.card D.Variables=D.q+2 := by
  rw [Fintype.card_coe,D.offsets_card]

abbrev FullRing (k : Type*) [CommRing k] := MvPolynomial D.Variables k
abbrev EndpointRing (_D : NSP14.SmallEmbedding.ThreeData) (k : Type*) [CommRing k] := MvPolynomial (Fin 2) k
abbrev InternalRing (k : Type*) [CommRing k] := MvPolynomial D.a k

def xVariable : D.Variables := ⟨0,by simp⟩
def vVariable : D.Variables := ⟨D.u,by simp⟩
def internalVariable (b : D.a) : D.Variables := ⟨b.val,by simp [b.property]⟩
def endpointVariable (i : Fin 2) : D.Variables := if i.val=0 then D.xVariable else D.vVariable

theorem endpointVariable_injective : Function.Injective D.endpointVariable := by
  intro a b h
  have ha2 := a.isLt
  have hb2 := b.isLt
  by_cases ha : a.val=0
  · by_cases hb : b.val=0
    · apply Fin.ext;omega
    · have hv := congrArg (fun z : D.Variables => z.val) h
      simp only [endpointVariable,ha,hb,ite_true,ite_false,xVariable,vVariable] at hv
      have := D.u_pos
      omega
  · by_cases hb : b.val=0
    · have hv := congrArg (fun z : D.Variables => z.val) h
      simp only [endpointVariable,ha,hb,ite_true,ite_false,xVariable,vVariable] at hv
      have := D.u_pos
      omega
    · apply Fin.ext;omega

theorem internalVariable_injective : Function.Injective D.internalVariable := by
  intro a b h
  exact Subtype.ext (congrArg (fun z : D.Variables => z.val) h)

variable (k : Type) [Field k]
noncomputable def fullPolynomialEquiv : D.FullRing k ≃ₐ[k] D.source.FullPolynomialRing k :=
  MvPolynomial.renameEquiv k D.atomVariableEquiv

noncomputable def fullToG : D.FullRing k →ₐ[k] D.source.TangentAlgebra k :=
  (D.source.fullPolynomialToG k).comp (D.fullPolynomialEquiv k).toAlgHom

noncomputable def endpointToFull : D.EndpointRing k →ₐ[k] D.FullRing k :=
  MvPolynomial.rename D.endpointVariable

noncomputable def internalToFull : D.InternalRing k →ₐ[k] D.FullRing k :=
  MvPolynomial.rename D.internalVariable

noncomputable def endpointToG : D.EndpointRing k →ₐ[k] D.source.TangentAlgebra k :=
  (D.fullToG k).comp (D.endpointToFull k)

noncomputable def internalToG : D.InternalRing k →ₐ[k] D.source.TangentAlgebra k :=
  (D.fullToG k).comp (D.internalToFull k)

theorem fullToG_X (b : D.Variables) :
    D.fullToG k (MvPolynomial.X b)=D.source.initialMonomial k (D.atomVariable b).val := by
  change D.source.fullPolynomialToG k ((D.fullPolynomialEquiv k) (MvPolynomial.X b))=_
  rw [fullPolynomialEquiv,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X,D.source.fullPolynomialToG_X]
  rfl

theorem endpointToFull_injective : Function.Injective (D.endpointToFull k) :=
  MvPolynomial.rename_injective _ D.endpointVariable_injective

theorem internalToFull_injective : Function.Injective (D.internalToFull k) :=
  MvPolynomial.rename_injective _ D.internalVariable_injective

/-- Actual G with the same minimal variables renamed; no independent
polynomial action or unproved presentation is supplied to this module. -/
noncomputable def fullG : ModuleCat (D.FullRing k) :=
  (ModuleCat.restrictScalars (D.fullPolynomialEquiv k).toRingEquiv.toRingHom).obj
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k))

noncomputable instance fullG_finite : Module.Finite (D.FullRing k) (D.fullG k) :=
  polynomialEquivRestricted_finite k D.Variables D.source.AtomExponent
    (D.fullPolynomialEquiv k)
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k))

theorem fullG_totalBetti (i : ℕ) :
    totalBetti k D.Variables (D.fullG k) i=
      totalBetti k D.source.AtomExponent
        (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i := by
  exact (polynomialEquivBettiIso k D.Variables D.source.AtomExponent
    (D.fullPolynomialEquiv k)
    (augmentation_rename k D.Variables D.source.AtomExponent D.atomVariableEquiv)
    (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.TangentAlgebra k)) i).toLinearEquiv.finrank_eq
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Core; source SHA256 71d86ba9ee508e849329628c8c76d38e66281a3aa07925da97db7cb01c1b524c.
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

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
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CoreMap; source SHA256 496e0413b459c8eb9b4942ef66458e6fc05468a8dfa93197d5118783fcd22c28.
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

noncomputable def coreAtomPoint (a : D.source.AtomExponent) : D.corePoints :=
  D.coreGeneratorPoint (D.atomVariableEquiv.symm a)

theorem coreAtomPoint_degree (a : D.source.AtomExponent) : D.coreDegree (D.coreAtomPoint a)=1 := rfl

theorem coreGeneratorPoint_value (b : D.Variables) :
    D.coreValue (D.coreGeneratorPoint b)=(D.atomVariable b).val := by
  apply Subtype.ext
  change 1*D.m+b.val*D.d=D.m+b.val*D.d
  rw [one_mul]

theorem coreAtomPoint_value (a : D.source.AtomExponent) : D.coreValue (D.coreAtomPoint a)=a.val := by
  rw [coreAtomPoint,D.coreGeneratorPoint_value]
  change (D.atomVariableEquiv (D.atomVariableEquiv.symm a)).val=a.val
  rw [Equiv.apply_symm_apply]

theorem exists_corePoint (a : D.source.carrier) :
    ∃ p : D.corePoints,D.coreDegree p=D.source.order a.val ∧ D.coreValue p=a := by
  obtain ⟨f,hf,hs⟩ := D.source.order_realized_by_atoms a.property
  let pts : Fin (D.source.order a.val) → D.corePoints :=
    fun i => D.coreAtomPoint ⟨⟨f i,(hf i).1⟩,hf i⟩
  let p : D.corePoints := ∑ i,pts i
  have hpd : D.coreDegree p=D.source.order a.val := by
    simp only [p,map_sum,pts,D.coreAtomPoint_degree,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_one]
  have hpv : D.coreValue p=a := by
    apply Subtype.ext
    simp only [p,map_sum,pts,D.coreAtomPoint_value]
    change D.source.carrier.subtype (∑ i,(⟨f i,(hf i).1⟩ : D.source.carrier))=a.val
    rw [map_sum]
    exact hs
  exact ⟨p,hpd,hpv⟩

variable (k : Type) [Field k]

theorem exists_coreInitial (a : D.source.carrier) :
    ∃ p : D.corePoints,D.coreInitial k p=D.source.initialMonomial k a := by
  obtain ⟨p,hpd,hpv⟩ := D.exists_corePoint a
  refine ⟨p,?_⟩
  unfold coreInitial NumericalSemigroup.initialMonomial
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply D.source.homogeneous_mk_eq k hpd
  change AddMonoidAlgebra.single (D.coreValue p) (1:k)=AddMonoidAlgebra.single a (1:k)
  rw [hpv]

/-- Surjectivity onto the original actual graded algebra, from maximal
minimal-atom representations and its genuine monomial basis. -/
theorem coreToG_surjective : Function.Surjective (D.coreToG k) := by
  have hr : (D.coreToG k).toLinearMap.range=⊤ := by
    apply top_unique
    rw [← (D.source.tangentBasis k).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    rw [D.source.tangentBasis_eq_initial]
    obtain ⟨p,hp⟩ := D.exists_coreInitial k a
    exact ⟨D.coreMonomial k p,(D.coreToG_monomial k p).trans hp⟩
  exact LinearMap.range_eq_top.mp hr

noncomputable def fullToCore : D.FullRing k →ₐ[k] D.Core k :=
  MvPolynomial.aeval (fun b => D.coreMonomial k (D.coreGeneratorPoint b))

theorem coreInitial_generator (b : D.Variables) :
    D.coreInitial k (D.coreGeneratorPoint b)=D.source.initialMonomial k (D.atomVariable b).val := by
  have ho : D.source.order (D.atomVariable b).val.val=1 := D.source.atom_order (D.atomVariable b).property
  unfold coreInitial NumericalSemigroup.initialMonomial
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply D.source.homogeneous_mk_eq k (show D.coreDegree (D.coreGeneratorPoint b)=D.source.order (D.atomVariable b).val.val from ho.symm)
  change AddMonoidAlgebra.single (D.coreValue (D.coreGeneratorPoint b)) (1:k)=AddMonoidAlgebra.single (D.atomVariable b).val (1:k)
  rw [D.coreGeneratorPoint_value]

theorem coreToG_fullToCore : (D.coreToG k).comp (D.fullToCore k)=D.fullToG k := by
  apply MvPolynomial.algHom_ext
  intro b
  simp only [AlgHom.comp_apply,fullToCore,MvPolynomial.aeval_X,D.coreToG_monomial,
    D.coreInitial_generator,D.fullToG_X]
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CoreKernel; source SHA256 398055ad9e11f3f8b724185135e3ae79494fa5348515713e632f2adb6761f49e.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem liveValue_injective (p q : D.corePoints)
    (hp : D.coreDegree p=D.source.order (D.coreValue p).val)
    (hq : D.coreDegree q=D.source.order (D.coreValue q).val)
    (hv : D.coreValue p=D.coreValue q) : p=q := by
  have hn : p.val.1=q.val.1 := hp.trans ((congrArg (fun a : D.source.carrier => D.source.order a.val) hv).trans hq.symm)
  have he := congrArg Subtype.val hv
  change p.val.1*D.m+p.val.2*D.d=q.val.1*D.m+q.val.2*D.d at he
  have hB : p.val.2=q.val.2 := by have := D.d_pos;rw [hn] at he;nlinarith
  exact Subtype.ext (Prod.ext hn hB)

variable (k : Type) [Field k]

theorem coreInitial_live (p : D.corePoints) (hp : D.coreDegree p=D.source.order (D.coreValue p).val) :
    D.coreInitial k p=D.source.initialMonomial k (D.coreValue p) := by
  unfold coreInitial NumericalSemigroup.initialMonomial
  apply DirectSum.of_eq_of_gradedMonoid_eq
  apply D.source.homogeneous_mk_eq k hp
  rfl

theorem coreToG_live_coefficient (p : D.corePoints)
    (hp : D.coreDegree p=D.source.order (D.coreValue p).val) (f : D.Core k) :
    D.source.tangentCoordinates k (D.coreToG k f) (D.coreValue p)=f.coeff p := by
  induction f using AddMonoidAlgebra.induction_on with
  | of q =>
    change D.source.tangentCoordinates k (D.coreToG k (D.coreMonomial k q)) (D.coreValue p)=_
    by_cases hq : D.coreDegree q=D.source.order (D.coreValue q).val
    · rw [D.coreToG_monomial,D.coreInitial_live k q hq,D.source.tangentCoordinates_initial]
      have hi : D.coreValue q=D.coreValue p ↔ q=p :=
        ⟨D.liveValue_injective q p hq hp,fun h => congrArg D.coreValue h⟩
      simp only [Finsupp.single_apply,AddMonoidAlgebra.of_apply,toAdd_ofAdd,AddMonoidAlgebra.coeff_single,hi]
    · have hlt : D.coreDegree q<D.source.order (D.coreValue q).val := by have := D.coreDegree_le_order q;omega
      rw [(D.coreToG_monomial_zero_iff k q).mpr hlt,map_zero,Finsupp.zero_apply]
      have hqp : q≠p := by rintro rfl;exact hq hp
      simp only [AddMonoidAlgebra.of_apply,toAdd_ofAdd,AddMonoidAlgebra.coeff_single,Finsupp.single_apply,hqp,ite_false]
  | add a b ha hb =>
    simp only [map_add,Finsupp.add_apply,AddMonoidAlgebra.coeff_add]
    rw [ha,hb]
  | smul c a ha =>
    simp only [map_smul,Finsupp.smul_apply,AddMonoidAlgebra.coeff_smul]
    rw [ha]

/-- Exact linear kernel of the actual graded ring surjection: only the
core monomials killed by a genuinely longer representation occur. -/
theorem coreToG_kernel_span : (D.coreToG k).toLinearMap.ker=
    Submodule.span k ((D.coreMonomial k) '' {p | D.coreDegree p<D.source.order (D.coreValue p).val}) := by
  apply le_antisymm
  · change (D.coreToG k).toLinearMap.ker ≤
      Submodule.span k ((fun p => AddMonoidAlgebra.single p (1:k)) '' {p | D.coreDegree p<D.source.order (D.coreValue p).val})
    rw [← AddMonoidAlgebra.supported_eq_span_single]
    intro f hf
    rw [AddMonoidAlgebra.mem_supported']
    intro p hp
    have he : D.coreDegree p=D.source.order (D.coreValue p).val := by
      have := D.coreDegree_le_order p
      change ¬D.coreDegree p<D.source.order (D.coreValue p).val at hp
      omega
    have hc := D.coreToG_live_coefficient k p he f
    change D.coreToG k f=0 at hf
    rw [hf,map_zero,Finsupp.zero_apply] at hc
    exact hc.symm
  · apply Submodule.span_le.mpr
    rintro _ ⟨p,hp,rfl⟩
    exact (D.coreToG_monomial_zero_iff k p).mpr hp
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Coordinates; source SHA256 1a5f332c3dc4026f9da8697778ca67f96aac02d9441b3581715da23ee1cd2226.
set_option backward.isDefEq.respectTransparency false
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

def epsilon (r : Fin D.u) : ℕ := if r.val=0 then 0 else 1
abbrev Coordinate := Fin D.u×ℕ×ℕ

def decodeCoordinate (c : D.Coordinate) : ℕ×ℕ :=
  (c.2.1+c.2.2+D.epsilon c.1,c.1.val+D.u*c.2.2)

def residue (p : D.corePoints) : Fin D.u := ⟨p.val.2%D.u,Nat.mod_lt _ D.u_pos⟩

theorem coordinate_budget (p : D.corePoints) : p.val.2/D.u+D.epsilon (D.residue p)≤p.val.1 := by
  have hd := Nat.mod_add_div p.val.2 D.u
  have hb := D.corePoint_bound p.property
  have hu := D.u_pos
  change p.val.2/D.u+(if p.val.2%D.u=0 then 0 else 1)≤p.val.1
  split_ifs with h0
  · by_contra h
    have hk : p.val.1+1≤p.val.2/D.u := by omega
    have hmul := Nat.mul_le_mul_left D.u hk
    nlinarith
  · by_contra h
    have hk : p.val.1≤p.val.2/D.u := by omega
    have hmul := Nat.mul_le_mul_left D.u hk
    have hr : 0 < p.val.2%D.u := Nat.pos_of_ne_zero h0
    nlinarith

def coreCoordinates (p : D.corePoints) : D.Coordinate :=
  (D.residue p,p.val.1-p.val.2/D.u-D.epsilon (D.residue p),p.val.2/D.u)

theorem decode_coreCoordinates (p : D.corePoints) : D.decodeCoordinate (D.coreCoordinates p)=p.val := by
  apply Prod.ext
  · change p.val.1-p.val.2/D.u-D.epsilon (D.residue p)+p.val.2/D.u+D.epsilon (D.residue p)=p.val.1
    have := D.coordinate_budget p
    omega
  · exact Nat.mod_add_div p.val.2 D.u

theorem decodeCoordinate_injective : Function.Injective D.decodeCoordinate := by
  rintro ⟨r,L,K⟩ ⟨s,A,B⟩ h
  have he : r.val+D.u*K=s.val+D.u*B := congrArg Prod.snd h
  have hr : r=s := by
    apply Fin.ext
    have hm := congrArg (fun n => n%D.u) he
    simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt,Nat.mod_eq_of_lt s.isLt] using hm
  subst s
  have hk : K=B := Nat.eq_of_mul_eq_mul_left D.u_pos (by omega)
  subst B
  have hL : L=A := by
    have hn := congrArg Prod.fst h
    change L+K+D.epsilon r=A+K+D.epsilon r at hn
    omega
  subst A
  rfl

/-- The indices are actual core points in these nonnegative coordinates.
No claim that all triples occur, or that residues are subalgebras. -/
def CoordinatePoint := {c : D.Coordinate // D.decodeCoordinate c∈D.corePoints}

def coreCoordinateEquiv : D.corePoints ≃ D.CoordinatePoint where
  toFun p := ⟨D.coreCoordinates p,by rw [D.decode_coreCoordinates];exact p.property⟩
  invFun c := ⟨D.decodeCoordinate c.val,c.property⟩
  left_inv p := Subtype.ext (D.decode_coreCoordinates p)
  right_inv c := by
    apply Subtype.ext
    apply D.decodeCoordinate_injective
    exact D.decode_coreCoordinates ⟨D.decodeCoordinate c.val,c.property⟩
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Competitors; source SHA256 f1e07912286b16ac29977bddb339a965b0028d983f6434e24468dfd4f4d7d2b0.
set_option backward.isDefEq.respectTransparency false
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

/-- Equality of actual numerical exponents forces every longer core
representation to be one of the j-th competitors, with j>=1. -/
theorem longer_core_pair (p q : D.corePoints) (hv : D.coreValue p=D.coreValue q)
    (hl : D.coreDegree p<D.coreDegree q) :
    ∃ j : ℕ,1≤j ∧ D.coreDegree q=D.coreDegree p+j*D.d ∧
      D.coreOffset p=D.coreOffset q+j*D.m := by
  have he := congrArg Subtype.val hv
  change D.coreDegree p*D.m+D.coreOffset p*D.d=
    D.coreDegree q*D.m+D.coreOffset q*D.d at he
  have hm : D.coreDegree p*D.m ≡ D.coreDegree q*D.m [MOD D.d] := by
    have h := congrArg (fun n => n%D.d) he
    change (D.coreDegree p*D.m)%D.d=(D.coreDegree q*D.m)%D.d
    simpa only [Nat.add_mod,Nat.mul_mod_left,Nat.add_zero,Nat.mod_mod] using h
  have hc := hm.cancel_right_of_coprime D.coprime.symm.gcd_eq_one
  obtain ⟨j,hj⟩ := hc.dvd'
  have hsub := Nat.sub_add_cancel hl.le
  have hdeg : D.coreDegree q=D.coreDegree p+j*D.d := by nlinarith only [hj,hsub]
  have hjpos : 1≤j := by
    by_cases hj0 : j=0
    · simp only [hj0,zero_mul,add_zero] at hdeg
      omega
    · omega
  refine ⟨j,hjpos,hdeg,?_⟩
  rw [hdeg] at he
  apply Nat.eq_of_mul_eq_mul_left D.d_pos
  nlinarith only [he]

/-- All competitors, not merely j=1, characterize the actual kernel.
The longer pair must itself belong to the genuine core. -/
theorem core_dead_iff_competitor (p : D.corePoints) :
    D.coreDegree p<D.source.order (D.coreValue p).val ↔
      ∃ j : ℕ,1≤j ∧ ∃ q : D.corePoints,
        D.coreDegree q=D.coreDegree p+j*D.d ∧ D.coreOffset p=D.coreOffset q+j*D.m := by
  constructor
  · intro hp
    obtain ⟨q,hqd,hqv⟩ := D.exists_corePoint (D.coreValue p)
    obtain ⟨j,hj,hd,hB⟩ := D.longer_core_pair p q hqv.symm (by omega)
    exact ⟨j,hj,q,hd,hB⟩
  · rintro ⟨j,hj,q,hd,hB⟩
    have hv : D.coreValue q=D.coreValue p := by
      apply Subtype.ext
      change D.coreDegree q*D.m+D.coreOffset q*D.d=
        D.coreDegree p*D.m+D.coreOffset p*D.d
      rw [hd,hB]
      ring
    have hb := D.coreDegree_le_order q
    rw [hv] at hb
    have hpos : 0 < j*D.d := Nat.mul_pos (by omega) (by have := D.d_pos;omega)
    omega
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Fibers; source SHA256 6890dd7116c9412d962902e5a376af3ee9b9fa4fb770fcbba1e42c88b874057e.
set_option backward.isDefEq.respectTransparency false
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

def coreFiber (r : Fin D.u) : Set (ℕ×ℕ) :=
  {c | D.decodeCoordinate (r,c)∈D.corePoints}

def coreEndpointPoint (c : ℕ×ℕ) : D.corePoints :=
  c.1 • D.coreGeneratorPoint D.xVariable+c.2 • D.coreGeneratorPoint D.vVariable

theorem coreEndpointPoint_coe (c : ℕ×ℕ) : (D.coreEndpointPoint c).val=(c.1+c.2,D.u*c.2) := by
  apply Prod.ext
  · simp [coreEndpointPoint,coreGeneratorPoint,xVariable,vVariable]
  · simp [coreEndpointPoint,coreGeneratorPoint,xVariable,vVariable,mul_comm]

theorem coreFiber_add (r : Fin D.u) {a : ℕ×ℕ} (ha : a∈D.coreFiber r) (b : ℕ×ℕ) :
    (a.1+b.1,a.2+b.2)∈D.coreFiber r := by
  have h := D.corePoints.add_mem ha (D.coreEndpointPoint b).property
  rw [D.coreEndpointPoint_coe] at h
  change D.decodeCoordinate (r,(a.1+b.1,a.2+b.2))∈D.corePoints
  convert h using 1
  apply Prod.ext
  · dsimp [decodeCoordinate];ring
  · dsimp [decodeCoordinate];ring

theorem coreFiber_upward (r : Fin D.u) {a b : ℕ×ℕ} (ha : a∈D.coreFiber r) (hab : a≤b) :
    b∈D.coreFiber r := by
  have h := D.coreFiber_add r ha (b.1-a.1,b.2-a.2)
  simpa only [Nat.add_sub_of_le hab.1,Nat.add_sub_of_le hab.2] using h

theorem coreFiber_zero (c : ℕ×ℕ) : c∈D.coreFiber ⟨0,D.u_pos⟩ := by
  have h0 : (0,0)∈D.coreFiber ⟨0,D.u_pos⟩ := by
    change D.decodeCoordinate (⟨0,D.u_pos⟩,(0,0))∈D.corePoints
    rw [show D.decodeCoordinate (⟨0,D.u_pos⟩,(0,0))=0 by simp [decodeCoordinate,epsilon]]
    exact D.corePoints.zero_mem
  exact D.coreFiber_upward _ h0 ⟨Nat.zero_le _,Nat.zero_le _⟩

def coreFiberExponents (r : Fin D.u) : Set (Fin 2 →₀ ℕ) :=
  {b | (b 0,b 1)∈D.coreFiber r}

variable (k : Type) [Field k]
noncomputable def coreFiberIdeal (r : Fin D.u) : Ideal (D.EndpointRing k) :=
  Ideal.span ((fun b => MvPolynomial.monomial b (1:k)) '' D.coreFiberExponents r)

theorem coreFiberIdeal_mem (r : Fin D.u) (f : D.EndpointRing k) :
    f∈D.coreFiberIdeal k r ↔ ∀ b∈f.support,(b 0,b 1)∈D.coreFiber r := by
  rw [coreFiberIdeal,MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h b hb
    obtain ⟨c,hc,hcb⟩ := h b hb
    exact D.coreFiber_upward r hc ⟨hcb 0,hcb 1⟩
  · intro h b hb
    exact ⟨b,h b hb,le_rfl⟩

theorem coreFiberIdeal_zero : D.coreFiberIdeal k ⟨0,D.u_pos⟩=⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [D.coreFiberIdeal_mem]
  intro b _
  exact D.coreFiber_zero (b 0,b 1)
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Carry; source SHA256 95ba789f8bcdb85db4e7cec6072cf197f1eec1ba532163180d0c8e932d9d0702.

namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

def shiftedResidue (r : Fin D.u) (j : ℕ) : Fin D.u :=
  ⟨(r.val+j*D.m)%D.u,Nat.mod_lt _ D.u_pos⟩

def carry (r : Fin D.u) (j : ℕ) : ℕ := (r.val+j*D.m)/D.u

theorem carry_eq (r : Fin D.u) (j : ℕ) :
    r.val+j*D.m=(D.shiftedResidue r j).val+D.u*D.carry r j :=
  (Nat.mod_add_div (r.val+j*D.m) D.u).symm

theorem carry_pos (r : Fin D.u) (j : ℕ) (hj : 1≤j) : 1≤D.carry r j := by
  apply (Nat.le_div_iff_mul_le D.u_pos).mpr
  have hm := Nat.mul_le_mul_right D.m hj
  have := D.u_lt
  change 1*D.u≤r.val+j*D.m
  omega

theorem epsilon_le_one (r : Fin D.u) : D.epsilon r≤1 := by
  unfold epsilon
  split_ifs <;> omega

/-- Natural-number form of c-epsilon_r+epsilon_s >= floor(j*m/u),
so no signed contribution is lost by truncated subtraction. -/
theorem carry_epsilon_lower (r : Fin D.u) (j : ℕ) :
    j*D.m/D.u+D.epsilon r≤D.carry r j+D.epsilon (D.shiftedResidue r j) := by
  have hle : j*D.m/D.u≤D.carry r j :=
    Nat.div_le_div_right (Nat.le_add_left (j*D.m) r.val)
  by_cases he : D.carry r j=j*D.m/D.u
  · have hc := D.carry_eq r j
    have hd := Nat.mod_add_div (j*D.m) D.u
    rw [he] at hc
    have hrs : r.val≤(D.shiftedResidue r j).val := by omega
    by_cases hr : r.val=0
    · have hε : D.epsilon r=0 := by simp only [epsilon,hr,ite_true]
      rw [he,hε,add_zero]
      omega
    · have hs : (D.shiftedResidue r j).val≠0 := by omega
      simp only [epsilon,hr,hs,ite_false]
      omega
  · have hε := D.epsilon_le_one r
    omega

/-- The first coordinate is computed in Z and only then clamped. -/
def forbiddenStart (r : Fin D.u) (j : ℕ) (c : ℕ×ℕ) : ℕ×ℕ :=
  (((c.1 : ℤ)-(j*D.d+D.carry r j+D.epsilon (D.shiftedResidue r j) : ℕ)+
      (D.epsilon r : ℤ)).toNat,c.2+D.carry r j)

theorem forbiddenStart_first_le (r : Fin D.u) (j : ℕ) (c : ℕ×ℕ) (A : ℕ) :
    (D.forbiddenStart r j c).1≤A ↔
      c.1+D.epsilon r≤A+j*D.d+D.carry r j+D.epsilon (D.shiftedResidue r j) := by
  unfold forbiddenStart
  rw [Int.toNat_le]
  omega

theorem forbiddenStart_le (r : Fin D.u) (j : ℕ) (c p : ℕ×ℕ) :
    D.forbiddenStart r j c≤p ↔
      c.1+D.epsilon r≤p.1+j*D.d+D.carry r j+D.epsilon (D.shiftedResidue r j) ∧
        c.2+D.carry r j≤p.2 := by
  change (D.forbiddenStart r j c).1≤p.1 ∧ (D.forbiddenStart r j c).2≤p.2 ↔ _
  rw [D.forbiddenStart_first_le]
  rfl

theorem floor_jm_ge (j : ℕ) : j≤j*D.m/D.u := by
  apply (Nat.le_div_iff_mul_le D.u_pos).mpr
  exact Nat.mul_le_mul_left j D.u_lt.le

/-- Uniform decay, with Nat subtraction denoting max(H-2*j,0).
This proof applies to every m,d satisfying the broad EH. -/
theorem forbiddenStart_height (r : Fin D.u) (j L K H : ℕ) (hL : L≤H) :
    (D.forbiddenStart r j (L,K)).1≤H-2*j := by
  apply (D.forbiddenStart_first_le r j (L,K) (H-2*j)).mpr
  have hc := D.carry_epsilon_lower r j
  have hf := D.floor_jm_ge j
  have hd : j≤j*D.d := by simpa only [mul_one] using Nat.mul_le_mul_left j D.d_pos
  omega
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.ActualKernel; source SHA256 9fcb8b751d540d92bd3d0c729109ad1001af913fc44a410d6b74150ad78c9c43.
set_option backward.isDefEq.respectTransparency false
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

/-- All long-side points and all positive competitors. Finite minimal
lists and stopping will be derived, rather than assumed in this set. -/
def competitorFiber (s : Fin D.u) : Set (ℕ×ℕ) :=
  {p | ∃ r : Fin D.u,∃ j : ℕ,1≤j ∧ ∃ c : ℕ×ℕ,c∈D.coreFiber r ∧
    D.shiftedResidue r j=s ∧ D.forbiddenStart r j c≤p}

/-- The real order test on the same actual numerical source. -/
def actualDeadFiber (s : Fin D.u) : Set (ℕ×ℕ) :=
  {c | c∈D.coreFiber s ∧ (D.decodeCoordinate (s,c)).1<
    D.source.order ((D.decodeCoordinate (s,c)).1*D.m+(D.decodeCoordinate (s,c)).2*D.d)}

theorem competitorFiber_upward (s : Fin D.u) {a b : ℕ×ℕ}
    (ha : a∈D.competitorFiber s) (hab : a≤b) : b∈D.competitorFiber s := by
  obtain ⟨r,j,hj,c,hc,hs,hstart⟩ := ha
  exact ⟨r,j,hj,c,hc,hs,hstart.trans hab⟩

theorem actual_dead_iff_forbidden (s : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber s) :
    (D.decodeCoordinate (s,c)).1<
      D.source.order ((D.decodeCoordinate (s,c)).1*D.m+(D.decodeCoordinate (s,c)).2*D.d) ↔
        c∈D.competitorFiber s := by
  let p : D.corePoints := ⟨D.decodeCoordinate (s,c),hc⟩
  change D.coreDegree p<D.source.order (D.coreValue p).val ↔ _
  constructor
  · intro hdead
    obtain ⟨j,hj,q,hdeg,hoff⟩ := (D.core_dead_iff_competitor p).mp hdead
    let g := D.coreCoordinates q
    let r := g.1
    let L := g.2.1
    let K := g.2.2
    have hqcoord : D.decodeCoordinate (r,(L,K))=q.val := D.decode_coreCoordinates q
    have hnq : L+K+D.epsilon r=D.coreDegree q := congrArg Prod.fst hqcoord
    have hBq : r.val+D.u*K=D.coreOffset q := congrArg Prod.snd hqcoord
    change D.coreDegree q=c.1+c.2+D.epsilon s+j*D.d at hdeg
    change s.val+D.u*c.2=D.coreOffset q+j*D.m at hoff
    have hnum : r.val+j*D.m+D.u*K=s.val+D.u*c.2 := by omega
    have hs : D.shiftedResidue r j=s := by
      apply Fin.ext
      have hmod := congrArg (fun n => n%D.u) hnum
      change (r.val+j*D.m)%D.u=s.val
      simpa only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt s.isLt] using hmod
    have hb : c.2=K+D.carry r j := by
      have hcar := D.carry_eq r j
      rw [hs] at hcar
      apply Nat.eq_of_mul_eq_mul_left D.u_pos
      nlinarith only [hnum,hcar]
    refine ⟨r,j,hj,(L,K),?_,hs,?_⟩
    · change D.decodeCoordinate (r,(L,K))∈D.corePoints
      rw [hqcoord]
      exact q.property
    · apply (D.forbiddenStart_le r j (L,K) c).mpr
      rw [hs]
      constructor <;> dsimp only
      · omega
      · omega
  · rintro ⟨r,j,hj,⟨L,K⟩,hM,hs,hstart⟩
    have hstarts := (D.forbiddenStart_le r j (L,K) c).mp hstart
    rw [hs] at hstarts
    have hε := D.epsilon_le_one r
    have hcarry := D.carry_pos r j hj
    let A := c.1+j*D.d+D.carry r j+D.epsilon s-D.epsilon r
    let B := c.2-D.carry r j
    have hA : A+D.epsilon r=c.1+j*D.d+D.carry r j+D.epsilon s :=
      Nat.sub_add_cancel (by omega)
    have hB : B+D.carry r j=c.2 := Nat.sub_add_cancel (by omega)
    have hMr : (A,B)∈D.coreFiber r := D.coreFiber_upward r hM ⟨by omega,by omega⟩
    let q : D.corePoints := ⟨D.decodeCoordinate (r,(A,B)),hMr⟩
    apply (D.core_dead_iff_competitor p).mpr
    refine ⟨j,hj,q,?_,?_⟩
    · change A+B+D.epsilon r=c.1+c.2+D.epsilon s+j*D.d
      omega
    · change s.val+D.u*c.2=r.val+D.u*B+j*D.m
      have hcar := D.carry_eq r j
      rw [hs] at hcar
      rw [← hB]
      nlinarith only [hcar]

/-- The exact actual kernel condition is M intersect T; the competitor
region alone is not the core or the kernel. -/
theorem actualDeadFiber_eq_inter (s : Fin D.u) :
    D.actualDeadFiber s=D.coreFiber s∩D.competitorFiber s := by
  ext c
  constructor
  · rintro ⟨hc,hdead⟩
    exact ⟨hc,(D.actual_dead_iff_forbidden s c hc).mp hdead⟩
  · rintro ⟨hc,hforbidden⟩
    exact ⟨hc,(D.actual_dead_iff_forbidden s c hc).mpr hforbidden⟩
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.KernelIdeals; source SHA256 b6984115f41354acb0338743aa4857c8c8e55f2b212e30aebe9bbb490decae96.

namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem actualDeadFiber_upward (s : Fin D.u) {a b : ℕ×ℕ}
    (ha : a∈D.actualDeadFiber s) (hab : a≤b) : b∈D.actualDeadFiber s := by
  rw [D.actualDeadFiber_eq_inter] at ha ⊢
  exact ⟨D.coreFiber_upward s ha.1 hab,D.competitorFiber_upward s ha.2 hab⟩

variable (k : Type) [Field k]
noncomputable def competitorIdeal (s : Fin D.u) : Ideal (D.EndpointRing k) :=
  NSP14.Endpoint.coordinateIdeal k (D.competitorFiber s)

/-- Defined by the actual order-killed core exponents, independently of
the forbidden-region ideal. The intersection equality is proved below. -/
noncomputable def actualKernelIdeal (s : Fin D.u) : Ideal (D.EndpointRing k) :=
  NSP14.Endpoint.coordinateIdeal k (D.actualDeadFiber s)

theorem actualKernelIdeal_eq_inf (s : Fin D.u) :
    D.actualKernelIdeal k s=D.coreFiberIdeal k s⊓D.competitorIdeal k s := by
  change NSP14.Endpoint.coordinateIdeal k (D.actualDeadFiber s)=_
  rw [D.actualDeadFiber_eq_inter,NSP14.Endpoint.coordinateIdeal_inter k _ _
    (D.coreFiber_upward s) (D.competitorFiber_upward s)]
  rfl

theorem actualKernelIdeal_mem (s : Fin D.u) (f : D.EndpointRing k) :
    f∈D.actualKernelIdeal k s ↔ ∀ b∈f.support,(b 0,b 1)∈D.actualDeadFiber s :=
  NSP14.Endpoint.coordinateIdeal_mem k (D.actualDeadFiber s) (D.actualDeadFiber_upward s) f
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.IdealCoordinates; source SHA256 068719e19892d289589ce4b3bc34df6e7b16e1c6f544d2e3f1f62b8a858d7dbf.
set_option backward.isDefEq.respectTransparency false
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def coreFiberCoefficients (r : Fin D.u) :
    (D.coreFiberIdeal k r) ≃ₗ[k] ({b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r} →₀ k) :=
  NSP14.Endpoint.coordinateIdealCoefficients k (D.coreFiber r) (D.coreFiber_upward r)
theorem coreFiberCoefficients_apply (r : Fin D.u) (f : D.coreFiberIdeal k r)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    D.coreFiberCoefficients k r f b=f.val.coeff b.val := rfl

end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.FiberIndices; source SHA256 e74715f81dc8dce79c979ade81ebe5e24d327ded349a16b1d48d742a34ba04e4.

namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)
def FiberPoint (r : Fin D.u) := {c : ℕ×ℕ // c∈D.coreFiber r}

noncomputable def fiberExponentEquiv (r : Fin D.u) :
    {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r} ≃ D.FiberPoint r where
  toFun b := ⟨(b.val 0,b.val 1),b.property⟩
  invFun c := ⟨NSP14.Endpoint.exponentPairEquiv c.val,by
    change (NSP14.Endpoint.exponentPairEquiv.symm (NSP14.Endpoint.exponentPairEquiv c.val))∈D.coreFiber r
    rw [AddEquiv.symm_apply_apply]
    exact c.property⟩
  left_inv b := Subtype.ext (NSP14.Endpoint.exponentPairEquiv.apply_symm_apply b.val)
  right_inv c := Subtype.ext (NSP14.Endpoint.exponentPairEquiv.symm_apply_apply c.val)

def coordinateFiberEquiv : D.CoordinatePoint ≃ (Σ r : Fin D.u,D.FiberPoint r) where
  toFun c := ⟨c.val.1,⟨c.val.2,c.property⟩⟩
  invFun c := ⟨(c.1,c.2.val),c.2.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (k : Type) [Field k]
noncomputable def coreFiberPairCoefficients (r : Fin D.u) :
    (D.coreFiberIdeal k r) ≃ₗ[k] (D.FiberPoint r →₀ k) :=
  (D.coreFiberCoefficients k r).trans (Finsupp.domLCongr (R:=k) (M:=k) (D.fiberExponentEquiv r))
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.IdealBasis; source SHA256 8fe6dbeda4e9baa9c322e0800ba735c8f6312999e2925f3550da3a0719bdacc7.
set_option backward.isDefEq.respectTransparency false
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def coreFiberBasis (r : Fin D.u) :
    Module.Basis {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r} k (D.coreFiberIdeal k r) :=
  NSP14.Endpoint.coordinateIdealBasis k (D.coreFiber r) (D.coreFiber_upward r)

theorem coreFiberBasis_val (r : Fin D.u)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    (D.coreFiberBasis k r b).val=MvPolynomial.monomial b.val (1:k) :=
  NSP14.Endpoint.coordinateIdealBasis_val k (D.coreFiber r) (D.coreFiber_upward r) b
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Modules; source SHA256 24bfcc996db37a5c43bddad1f2bcf509ce6fb64f71bd800e702173d1919c59b3.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def endpointToCore : D.EndpointRing k →ₐ[k] D.Core k :=
  (D.fullToCore k).comp (D.endpointToFull k)

theorem endpointToCore_X (i : Fin 2) :
    D.endpointToCore k (MvPolynomial.X i)=D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i)) := by
  simp only [endpointToCore,AlgHom.comp_apply,endpointToFull,MvPolynomial.rename_X,
    fullToCore,MvPolynomial.aeval_X]

theorem coreToG_endpointToCore : (D.coreToG k).comp (D.endpointToCore k)=D.endpointToG k := by
  rw [endpointToCore,← AlgHom.comp_assoc,D.coreToG_fullToCore]
  rfl

/-- The actual actions are attached to module objects, keeping other
Fin-2 cut actions on the same G out of the typeclass instance search. -/
noncomputable def coreEndpointModule : ModuleCat (D.EndpointRing k) :=
  polynomialRegularModule k (Fin 2) (D.Core k) (D.endpointToCore k)

noncomputable def actualEndpointModule : ModuleCat (D.EndpointRing k) :=
  polynomialRegularModule k (Fin 2) (D.source.TangentAlgebra k) (D.endpointToG k)

noncomputable def coreEndpointCoefficients :
    coefficientModule k (Fin 2) (D.coreEndpointModule k) ≃ₗ[k] D.Core k :=
  regularRestrictionCoefficientEquiv k (Fin 2) (D.Core k) (D.endpointToCore k)

noncomputable def actualEndpointCoefficients :
    coefficientModule k (Fin 2) (D.actualEndpointModule k) ≃ₗ[k] D.source.TangentAlgebra k :=
  regularRestrictionCoefficientEquiv k (Fin 2) (D.source.TangentAlgebra k) (D.endpointToG k)

noncomputable def coreToGEndpoint : D.coreEndpointModule k ⟶ D.actualEndpointModule k :=
  ModuleCat.ofHom (X:=D.coreEndpointModule k) (Y:=D.actualEndpointModule k) {
    toFun a := D.coreToG k (show D.Core k from a)
    map_add' a b := (D.coreToG k).map_add a b
    map_smul' p a := by
      change D.coreToG k (D.endpointToCore k p*(show D.Core k from a))=
        D.endpointToG k p*D.coreToG k (show D.Core k from a)
      rw [map_mul]
      have h := AlgHom.congr_fun (D.coreToG_endpointToCore k) p
      change D.coreToG k (D.endpointToCore k p)=D.endpointToG k p at h
      rw [h] }

theorem coreToGEndpoint_surjective : Function.Surjective (D.coreToGEndpoint k).hom := by
  intro a
  obtain ⟨b,hb⟩ := D.coreToG_surjective k (show D.source.TangentAlgebra k from a)
  exact ⟨b,hb⟩

theorem coreEndpoint_variable (i : Fin 2) (a : coefficientModule k (Fin 2) (D.coreEndpointModule k)) :
    D.coreEndpointCoefficients k ((MvPolynomial.X i : D.EndpointRing k) • a)=
      D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i))*D.coreEndpointCoefficients k a := by
  change D.endpointToCore k (MvPolynomial.X i)*(show D.Core k from a)=_
  rw [D.endpointToCore_X]
  rfl
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.FiberAssembly; source SHA256 a58bb8899bb88c51a4792db91762eaa1296624ba583eccc91d6a50e47d51d28d.
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

abbrev FiberBasisIndex := Σ r : Fin D.u,{b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}

noncomputable def fiberPolynomialIndexEquiv : D.FiberBasisIndex ≃ D.corePoints :=
  (Equiv.sigmaCongrRight (fun r => D.fiberExponentEquiv r)).trans
    (D.coordinateFiberEquiv.symm.trans D.coreCoordinateEquiv.symm)

def fiberPolynomialPoint (r : Fin D.u)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) : D.corePoints :=
  ⟨D.decodeCoordinate (r,(b.val 0,b.val 1)),b.property⟩

theorem fiberPolynomialIndexEquiv_apply (b : D.FiberBasisIndex) :
    D.fiberPolynomialIndexEquiv b=D.fiberPolynomialPoint b.1 b.2 := rfl

variable (k : Type) [Field k]
noncomputable def coreSumBasis : Module.Basis D.FiberBasisIndex k (⨁ r : Fin D.u,D.coreFiberIdeal k r) :=
  DFinsupp.basis (fun r => D.coreFiberBasis k r)

theorem coreSumBasis_apply (b : D.FiberBasisIndex) :
    D.coreSumBasis k b=DFinsupp.single b.1 (D.coreFiberBasis k b.1 b.2) := by
  apply (D.coreSumBasis k).repr.injective
  rw [Module.Basis.repr_self]
  symm
  change (sigmaFinsuppLequivDFinsupp k).symm
    (DFinsupp.mapRange (fun r a => (D.coreFiberBasis k r).repr a)
      (fun r => (D.coreFiberBasis k r).repr.map_zero)
      (DFinsupp.single b.1 (D.coreFiberBasis k b.1 b.2)))=Finsupp.single b 1
  rw [DFinsupp.mapRange_single,Module.Basis.repr_self]
  apply (sigmaFinsuppLequivDFinsupp k).symm_apply_eq.mpr
  exact (sigmaFinsuppEquivDFinsupp_single b (1:k)).symm

/-- The actual monomial-basis assembly before polynomial-linearity is
proved. Its source is a direct sum of genuine polynomial ideals. -/
noncomputable def coreFiberLinearAssembly : (⨁ r : Fin D.u,D.coreFiberIdeal k r) ≃ₗ[k] D.Core k :=
  (D.coreSumBasis k).equiv (AddMonoidAlgebra.basis D.corePoints k) D.fiberPolynomialIndexEquiv

theorem coreFiberLinearAssembly_basis (b : D.FiberBasisIndex) :
    D.coreFiberLinearAssembly k (D.coreSumBasis k b)=D.coreMonomial k (D.fiberPolynomialPoint b.1 b.2) := by
  rw [coreFiberLinearAssembly,Module.Basis.equiv_apply,D.fiberPolynomialIndexEquiv_apply]
  rfl
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.FiberAction; source SHA256 ab09bb63d0952ce28369c013a7e513f62aab49b18795a67e79bafd8250a7e64b.
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

noncomputable def fiberExponentStep (r : Fin D.u) (i : Fin 2)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r} :=
  ⟨b.val+Finsupp.single i 1,D.coreFiber_upward r b.property
    ⟨by simp only [Finsupp.add_apply];omega,by simp only [Finsupp.add_apply];omega⟩⟩

noncomputable def fiberIndexStep (i : Fin 2) (b : D.FiberBasisIndex) : D.FiberBasisIndex :=
  ⟨b.1,D.fiberExponentStep b.1 i b.2⟩

theorem fiberPolynomialPoint_step (r : Fin D.u) (i : Fin 2)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    D.fiberPolynomialPoint r (D.fiberExponentStep r i b)=
      D.fiberPolynomialPoint r b+D.coreGeneratorPoint (D.endpointVariable i) := by
  have hi : i=0 ∨ i=1 := by
    by_cases h : i.val=0
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext (by have := i.isLt;omega))
  rcases hi with rfl|rfl
  all_goals
    apply Subtype.ext
    apply Prod.ext
  all_goals
    simp [fiberPolynomialPoint,fiberExponentStep,decodeCoordinate,coreGeneratorPoint,
      endpointVariable,xVariable,vVariable]
  all_goals ring

variable (k : Type) [Field k]

theorem coreFiberBasis_X (r : Fin D.u) (i : Fin 2)
    (b : {b : Fin 2 →₀ ℕ // (b 0,b 1)∈D.coreFiber r}) :
    (MvPolynomial.X i : D.EndpointRing k) • D.coreFiberBasis k r b=
      D.coreFiberBasis k r (D.fiberExponentStep r i b) := by
  apply Subtype.ext
  change (MvPolynomial.X i : D.EndpointRing k)*(D.coreFiberBasis k r b).val=
    (D.coreFiberBasis k r (D.fiberExponentStep r i b)).val
  rw [D.coreFiberBasis_val,D.coreFiberBasis_val,MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul]
  change MvPolynomial.monomial (Finsupp.single i 1+b.val) (1:k)=
    MvPolynomial.monomial (b.val+Finsupp.single i 1) (1:k)
  rw [add_comm]

theorem coreSumBasis_X (i : Fin 2) (b : D.FiberBasisIndex) :
    (MvPolynomial.X i : D.EndpointRing k) • D.coreSumBasis k b=
      D.coreSumBasis k (D.fiberIndexStep i b) := by
  rw [D.coreSumBasis_apply,D.coreSumBasis_apply,← DFinsupp.single_smul,D.coreFiberBasis_X]
  rfl

theorem coreMonomial_mul (p q : D.corePoints) :
    D.coreMonomial k p*D.coreMonomial k q=D.coreMonomial k (p+q) := by
  simp only [coreMonomial,AddMonoidAlgebra.single_mul_single,one_mul]

/-- Compatibility is proved on the actual ideal monomial bases, and
then extended coefficient-linearly; no polynomial-linearity premise is added. -/
theorem coreFiberAssembly_variable (i : Fin 2) (a : ⨁ r : Fin D.u,D.coreFiberIdeal k r) :
    D.coreFiberLinearAssembly k ((MvPolynomial.X i : D.EndpointRing k) • a)=
      D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i))*D.coreFiberLinearAssembly k a := by
  have ha : a∈Submodule.span k (Set.range (D.coreSumBasis k)) := by
    rw [(D.coreSumBasis k).span_eq]
    trivial
  refine Submodule.span_induction (p:=fun a _ =>
    D.coreFiberLinearAssembly k ((MvPolynomial.X i : D.EndpointRing k) • a)=
      D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i))*D.coreFiberLinearAssembly k a) ?_ ?_ ?_ ?_ ha
  · rintro _ ⟨b,rfl⟩
    rw [D.coreSumBasis_X,D.coreFiberLinearAssembly_basis,D.coreFiberLinearAssembly_basis,
      D.coreMonomial_mul]
    change D.coreMonomial k (D.fiberPolynomialPoint b.1 (D.fiberExponentStep b.1 i b.2))=_
    rw [D.fiberPolynomialPoint_step,add_comm]
  · simp only [smul_zero,map_zero,mul_zero]
  · intro a b _ _ ha hb
    simp only [smul_add,map_add,mul_add,ha,hb]
  · intro c a _ ha
    rw [smul_comm (MvPolynomial.X i : D.EndpointRing k) c a,map_smul,ha,map_smul,mul_smul_comm]
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.FiberModule; source SHA256 1bd33e9c405b7e6d28c1868a6acc927d9fee86b1abf05676fd43124701a20382.
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
open CategoryTheory NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def fiberSumModule : ModuleCat (D.EndpointRing k) :=
  ModuleCat.of (D.EndpointRing k) (⨁ r : Fin D.u,D.coreFiberIdeal k r)

noncomputable def coreFiberCoefficientEquiv :
    coefficientModule k (Fin 2) (D.fiberSumModule k) ≃ₗ[k]
      coefficientModule k (Fin 2) (D.coreEndpointModule k) :=
  (originalCoefficientEquiv k (Fin 2) (⨁ r : Fin D.u,D.coreFiberIdeal k r)).trans
    ((D.coreFiberLinearAssembly k).trans (D.coreEndpointCoefficients k).symm)

theorem coreFiberCoefficient_variable (i : Fin 2)
    (a : coefficientModule k (Fin 2) (D.fiberSumModule k)) :
    D.coreFiberCoefficientEquiv k ((MvPolynomial.X i : D.EndpointRing k) • a)=
      (MvPolynomial.X i : D.EndpointRing k) • D.coreFiberCoefficientEquiv k a := by
  apply (D.coreEndpointCoefficients k).injective
  rw [D.coreEndpoint_variable]
  change D.coreFiberLinearAssembly k ((MvPolynomial.X i : D.EndpointRing k) •
    (show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from a))=
      D.coreMonomial k (D.coreGeneratorPoint (D.endpointVariable i))*
        D.coreFiberLinearAssembly k (show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from a)
  exact D.coreFiberAssembly_variable k i _

noncomputable def coreFiberAssembly : D.fiberSumModule k ⟶ D.coreEndpointModule k :=
  polynomialHomOfVariables k (Fin 2) (D.coreFiberCoefficientEquiv k).toLinearMap
    (D.coreFiberCoefficient_variable k)

/-- The actual E-module decomposition, with each component a genuine
ideal M_r. The monomial degree is L+K+epsilon_r, retained by its index. -/
noncomputable def coreFiberModuleEquiv : D.coreEndpointModule k ≃ₗ[D.EndpointRing k]
    (⨁ r : Fin D.u,D.coreFiberIdeal k r) :=
  (LinearEquiv.ofBijective (D.coreFiberAssembly k).hom (D.coreFiberCoefficientEquiv k).bijective).symm

noncomputable instance coreEndpointFinite : Module.Finite (D.EndpointRing k) (D.coreEndpointModule k) :=
  Module.Finite.equiv (D.coreFiberModuleEquiv k).symm

noncomputable instance actualEndpointFinite : Module.Finite (D.EndpointRing k) (D.actualEndpointModule k) :=
  Module.Finite.of_surjective (D.coreToGEndpoint k).hom (D.coreToGEndpoint_surjective k)
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.HomologyFinite; source SHA256 b154965a4eb69f27967bef50a6d486047a55894d5087e731e9b8c73503a33810.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory HomologicalComplex NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

/-- Ordered as v then x, so it is the actual v-cone on the actual
x-complex. The ordering is compared to ordinary E-Tor below. -/
noncomputable def endpointElements : List (D.source.TangentAlgebra k) :=
  [D.endpointToG k (MvPolynomial.X 1),D.endpointToG k (MvPolynomial.X 0)]

noncomputable def endpointComplex : ChainComplex (ModuleCat k) ℕ :=
  regularPartialCoefficientComplex k (D.source.TangentAlgebra k) (D.endpointElements k)

noncomputable def endpointPolynomialIso : D.endpointComplex k ≅
    (coefficientKoszulListFunctor k (Fin 2) [1,0]).obj (D.actualEndpointModule k) :=
  regularPartialPolynomialIso k (D.source.TangentAlgebra k) (Fin 2) (D.endpointToG k) [1,0]

noncomputable def endpointHomologyIso (i : ℕ) :
    (D.endpointComplex k).homology i ≅ koszulHomologyK k (Fin 2) (D.actualEndpointModule k) i :=
  (homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (D.endpointPolynomialIso k) ≪≫
    (fullListHomologyKIso k (Fin 2) [1,0] (by intro x;fin_cases x <;> simp) (by decide)
      (D.actualEndpointModule k) i).symm

/-- Only homology is finite over k. The chain groups retain the actual
infinite-dimensional tangent algebra. -/
noncomputable instance endpointHomologyFinite (i : ℕ) :
    Module.Finite k ((D.endpointComplex k).homology i) := by
  let := koszul_homology_finite k (Fin 2) (D.actualEndpointModule k) i
  exact Module.Finite.equiv (D.endpointHomologyIso k i).symm.toLinearEquiv

theorem endpointHomology_betti (i : ℕ) :
    Module.finrank k ((D.endpointComplex k).homology i)=
      totalBetti k (Fin 2) (D.actualEndpointModule k) i :=
  (D.endpointHomologyIso k i).toLinearEquiv.finrank_eq

theorem endpointHomology_above (i : ℕ) (hi : 2 < i) :
    Module.finrank k ((D.endpointComplex k).homology i)=0 := by
  rw [D.endpointHomology_betti]
  exact totalBetti_eq_zero_of_gt k (Fin 2) _ i (by simpa using hi)
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.ArtinQuotient; source SHA256 0ba1f2dc561865b715ba9c5bd1864708f5434d79d68b9b0f30a8aab7e1ff2f44.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

abbrev QCore := NSP14.Endpoint.EndpointQuotient k (D.Core k) (D.endpointToCore k)
abbrev QActual := NSP14.Endpoint.EndpointQuotient k (D.source.TangentAlgebra k) (D.endpointToG k)

noncomputable def actualH0QuotientEquiv : (D.endpointComplex k).homology 0 ≃ₗ[k] D.QActual k :=
  NSP14.Endpoint.endpointH0QuotientEquiv k (D.source.TangentAlgebra k) (D.endpointToG k)

noncomputable def actualP : ℕ := Module.finrank k (D.QActual k)
noncomputable def coreP : ℕ := Module.finrank k (D.QCore k)
noncomputable def actualR : ℕ := Module.finrank k ((D.endpointComplex k).homology 2)

theorem actualH0_dimension : Module.finrank k ((D.endpointComplex k).homology 0)=D.actualP k :=
  (D.actualH0QuotientEquiv k).finrank_eq
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.XHomology; source SHA256 dea50a0633a6901a0285a58e0221f34dc1612ca33bb276387303eec31d0411d0.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

theorem endpoint_xElement : D.endpointToG k (MvPolynomial.X 0)=D.source.xElement k := by
  rw [endpointToG,AlgHom.comp_apply,endpointToFull,MvPolynomial.rename_X]
  change D.fullToG k (MvPolynomial.X D.xVariable)=_
  rw [D.fullToG_X]
  unfold NumericalSemigroup.xElement
  apply congrArg (D.source.initialMonomial k)
  apply Subtype.ext
  change D.m+0*D.d=D.source.multiplicity
  simpa only [zero_mul,add_zero] using D.multiplicity.symm

noncomputable def xNativeComplex : ChainComplex (ModuleCat (D.source.TangentAlgebra k)) ℕ :=
  actionRegularComplex (D.source.TangentAlgebra k) [D.source.xElement k]

noncomputable def xComplex : ChainComplex (ModuleCat k) ℕ :=
  nativeCoefficientComplex k (D.source.TangentAlgebra k) (D.xNativeComplex k)

noncomputable def xNativeH0Equiv : (D.xNativeComplex k).homology 0 ≃ₗ[D.source.TangentAlgebra k]
    D.source.HeadAlgebra k :=
  (actionRegularH0Equiv (D.source.TangentAlgebra k) [D.source.xElement k]).trans
    (Submodule.quotEquivOfEq _ _ (by
      change Ideal.span {a : D.source.TangentAlgebra k | a∈[D.source.xElement k]}=D.source.xIdeal k
      congr 1
      ext a
      simp only [List.mem_singleton,Set.mem_ofPred_eq,Set.mem_singleton_iff]))

noncomputable def headNativeCoefficients : ModuleCat k :=
  (ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).obj
    (ModuleCat.of (D.source.TangentAlgebra k) (D.source.HeadAlgebra k))

noncomputable def headCoefficientEquiv : D.headNativeCoefficients k ≃ₗ[k] D.source.HeadAlgebra k where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    change (algebraMap k (D.source.TangentAlgebra k) c) • (show D.source.HeadAlgebra k from a)=
      c • (show D.source.HeadAlgebra k from a)
    rw [algebraMap_smul]

noncomputable def xH0Equiv : (D.xComplex k).homology 0 ≃ₗ[k] D.source.HeadAlgebra k :=
  (nativeCoefficientHomologyIso k (D.source.TangentAlgebra k) (D.xNativeComplex k) 0).toLinearEquiv.trans
    (((ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).mapIso
      (D.xNativeH0Equiv k).toModuleIso).toLinearEquiv.trans (D.headCoefficientEquiv k))

noncomputable def xNativeKernel : Submodule (D.source.TangentAlgebra k) (D.source.TangentAlgebra k) :=
  ((D.source.xElement k) • 𝟙 (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).hom.ker

noncomputable def xNativeKernelCoefficients : ModuleCat k :=
  (ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).obj
    (ModuleCat.of (D.source.TangentAlgebra k) (D.xNativeKernel k))

noncomputable def xKernelCoefficientEquiv : D.xNativeKernelCoefficients k ≃ₗ[k] (D.source.xMultiply k).ker where
  toFun a := ⟨a.val,by
    have h : D.source.xElement k*a.val=0 := a.property
    change a.val*D.source.xElement k=0
    rw [mul_comm]
    exact h⟩
  invFun a := ⟨a.val,by
    have h : a.val*D.source.xElement k=0 := a.property
    change D.source.xElement k*a.val=0
    rw [mul_comm]
    exact h⟩
  left_inv a := rfl
  right_inv a := rfl
  map_add' a b := rfl
  map_smul' c a := by
    apply Subtype.ext
    change (algebraMap k (D.source.TangentAlgebra k) c)*a.val=c • a.val
    exact (Algebra.smul_def c a.val).symm

noncomputable def xH1Equiv : (D.xComplex k).homology 1 ≃ₗ[k] (D.source.xMultiply k).ker :=
  (nativeCoefficientHomologyIso k (D.source.TangentAlgebra k) (D.xNativeComplex k) 1).toLinearEquiv.trans
    (((ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).mapIso
      (NSP14.Endpoint.singleActionH1Equiv (D.source.TangentAlgebra k) (D.source.xElement k)
        (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).toModuleIso).toLinearEquiv.trans
      (D.xKernelCoefficientEquiv k))

theorem xHomology_above (i : ℕ) (hi : 1 < i) : IsZero ((D.xComplex k).homology i) := by
  have hz : IsZero ((D.xNativeComplex k).homology i) :=
    HomologicalComplex.ExactAt.isZero_homology (HomologicalComplex.ExactAt.of_isZero
      (NSP14.Endpoint.action_piece_isZero_of_gt _ [_] _ i (by simpa using hi)))
  exact IsZero.of_iso ((ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).map_isZero hz)
    (nativeCoefficientHomologyIso k (D.source.TangentAlgebra k) (D.xNativeComplex k) i)

noncomputable instance xHomologyFinite (i : ℕ) : Module.Finite k ((D.xComplex k).homology i) := by
  cases i with
  | zero => exact Module.Finite.equiv (D.xH0Equiv k).symm
  | succ i =>
    cases i with
    | zero => exact Module.Finite.equiv (D.xH1Equiv k).symm
    | succ i =>
      have : Subsingleton ((D.xComplex k).homology (i+1+1)) :=
        ModuleCat.subsingleton_of_isZero (D.xHomology_above k _ (by omega))
      infer_instance
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.HomologyBalance; source SHA256 79caa0213e233ef3834c8db66130c361565eae60d1fbeb1d74f85fafc4b4210e.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits HomologicalComplex NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def vOnXComplex : D.xComplex k ⟶ D.xComplex k :=
  (nativeCoefficientFunctor k (D.source.TangentAlgebra k)).map
    (D.endpointToG k (MvPolynomial.X 1) • 𝟙 (D.xNativeComplex k))

noncomputable def endpointConeIso : D.endpointComplex k ≅ homotopyCofiber (D.vOnXComplex k) := by
  unfold endpointComplex endpointElements regularPartialCoefficientComplex
  rw [D.endpoint_xElement]
  exact homotopyCofiber.mapHomologicalComplexObjIso _
    (ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k)))

/-- Exact three-row Euler identity from the actual x-kernel/head and
the actual v-cone. In particular finrank(G) is never evaluated. -/
theorem endpointHomology_balance :
    Module.finrank k ((D.endpointComplex k).homology 1)=
      Module.finrank k ((D.endpointComplex k).homology 0)+
        Module.finrank k ((D.endpointComplex k).homology 2) := by
  have hz : Module.finrank k ((D.xComplex k).homology 2)=0 := by
    have : Subsingleton ((D.xComplex k).homology 2) :=
      ModuleCat.subsingleton_of_isZero (D.xHomology_above k 2 (by omega))
    exact Module.finrank_zero_of_subsingleton
  have h := NSP14.Endpoint.endomorphismCone_balance k (D.xComplex k) (D.vOnXComplex k) hz
  have he (i : ℕ) : Module.finrank k ((D.endpointComplex k).homology i)=
      Module.finrank k ((homotopyCofiber (D.vOnXComplex k)).homology i) :=
    ((homologyFunctor _ (ComplexShape.down ℕ) i).mapIso (D.endpointConeIso k)).toLinearEquiv.finrank_eq
  rw [←he 0,←he 1,←he 2] at h
  exact h
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.ArtinTransport; source SHA256 428f095a759b2818b3944a7732a922ee244b2f9126e179802ec656917dbb83e2.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable instance QCoreFinite : Module.Finite k (D.QCore k) := by
  let : Module.Finite (D.EndpointRing k)
      (polynomialRegularModule k (Fin 2) (D.Core k) (D.endpointToCore k)) := D.coreEndpointFinite k
  exact NSP14.Endpoint.endpointQuotientFinite k (D.Core k) (D.endpointToCore k)

noncomputable instance QActualFinite : Module.Finite k (D.QActual k) := by
  let : Module.Finite (D.EndpointRing k)
      (polynomialRegularModule k (Fin 2) (D.source.TangentAlgebra k) (D.endpointToG k)) := D.actualEndpointFinite k
  exact NSP14.Endpoint.endpointQuotientFinite k (D.source.TangentAlgebra k) (D.endpointToG k)

theorem core_endpointIdeal_le : NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k)≤
    Ideal.comap (D.coreToG k) (NSP14.Endpoint.endpointIdeal k (D.source.TangentAlgebra k) (D.endpointToG k)) := by
  apply Ideal.span_le.mpr
  intro a ha
  change D.coreToG k a∈NSP14.Endpoint.endpointIdeal k (D.source.TangentAlgebra k) (D.endpointToG k)
  have he (i : Fin 2) : D.coreToG k (D.endpointToCore k (MvPolynomial.X i))=D.endpointToG k (MvPolynomial.X i) :=
    AlgHom.congr_fun (D.coreToG_endpointToCore k) (MvPolynomial.X i)
  rcases (show a=D.endpointToCore k (MvPolynomial.X 1) ∨ a=D.endpointToCore k (MvPolynomial.X 0) by
    simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false,Set.mem_ofPred_eq] using ha) with rfl|rfl
  · rw [he]
    exact Ideal.subset_span (by simp)
  · rw [he]
    exact Ideal.subset_span (by simp)

/-- The genuine quotient map QC -> QG of the same core-to-G map. -/
noncomputable def QCoreToActual : D.QCore k →ₐ[k] D.QActual k :=
  Ideal.quotientMapₐ _ (D.coreToG k) (D.core_endpointIdeal_le k)

theorem QCoreToActual_surjective : Function.Surjective (D.QCoreToActual k) :=
  Ideal.quotientMap_surjective (H:=D.core_endpointIdeal_le k) (D.coreToG_surjective k)

noncomputable def internalToCore : D.InternalRing k →ₐ[k] D.Core k :=
  (D.fullToCore k).comp (D.internalToFull k)

noncomputable def internalToQCore : D.InternalRing k →ₐ[k] D.QCore k :=
  (Ideal.Quotient.mkₐ k _).comp (D.internalToCore k)

noncomputable def internalToQActual : D.InternalRing k →ₐ[k] D.QActual k :=
  (Ideal.Quotient.mkₐ k _).comp (D.internalToG k)

noncomputable def QCoreModule : ModuleCat (D.InternalRing k) :=
  polynomialRegularModule k D.a (D.QCore k) (D.internalToQCore k)

noncomputable def QActualModule : ModuleCat (D.InternalRing k) :=
  polynomialRegularModule k D.a (D.QActual k) (D.internalToQActual k)

noncomputable instance QCoreModuleFinite : Module.Finite (D.InternalRing k) (D.QCoreModule k) :=
  regularRestriction_finite k D.a _ _

noncomputable instance QActualModuleFinite : Module.Finite (D.InternalRing k) (D.QActualModule k) :=
  regularRestriction_finite k D.a _ _

theorem QCoreToActual_internal (p : D.InternalRing k) :
    D.QCoreToActual k (D.internalToQCore k p)=D.internalToQActual k p := by
  change Ideal.Quotient.mk _ (D.coreToG k (D.fullToCore k (D.internalToFull k p)))=
    Ideal.Quotient.mk _ (D.fullToG k (D.internalToFull k p))
  have he := AlgHom.congr_fun (D.coreToG_fullToCore k) (D.internalToFull k p)
  exact congrArg (Ideal.Quotient.mk _) he

noncomputable def QCoreToActualModule : D.QCoreModule k ⟶ D.QActualModule k :=
  ModuleCat.ofHom (X:=D.QCoreModule k) (Y:=D.QActualModule k) {
    toFun a := D.QCoreToActual k (show D.QCore k from a)
    map_add' a b := (D.QCoreToActual k).map_add a b
    map_smul' p a := by
      change D.QCoreToActual k (D.internalToQCore k p*(show D.QCore k from a))=
        D.internalToQActual k p*D.QCoreToActual k (show D.QCore k from a)
      rw [map_mul,D.QCoreToActual_internal] }

theorem actualH1_dimension : Module.finrank k ((D.endpointComplex k).homology 1)=D.actualP k+D.actualR k := by
  rw [D.endpointHomology_balance,D.actualH0_dimension]
  rfl
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.VariableOrder; source SHA256 90791667c74272d929ca109343c15e5e77d90f0b6219df8e083cd3cfc55f0a8d.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def internalVariableList : List D.a := variableList k D.a
noncomputable def fullVariableList : List D.Variables :=
  (D.internalVariableList k).map D.internalVariable++[D.vVariable,D.xVariable]

omit [Field k] in
theorem internalVariableList_length : (D.internalVariableList k).length=D.q := by
  simp only [internalVariableList,variableList_length,Fintype.card_coe,q]

omit [Field k] in
theorem fullVariableList_mem (b : D.Variables) : b∈D.fullVariableList k := by
  rcases (D.mem_offsets b.val).mp b.property with hb|hb|hb
  · apply List.mem_append_right
    have he : b=D.xVariable := Subtype.ext hb
    simp [he]
  · apply List.mem_append_right
    have he : b=D.vVariable := Subtype.ext hb
    simp [he]
  · apply List.mem_append_left
    exact List.mem_map.mpr ⟨⟨b.val,hb⟩,mem_variableList k D.a _,Subtype.ext rfl⟩

omit [Field k] in
theorem fullVariableList_nodup : (D.fullVariableList k).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨(variableList_nodup k D.a).map D.internalVariable_injective,?_,?_⟩
  · have hne : D.vVariable≠D.xVariable := by
      intro h
      have hv := congrArg Subtype.val h
      change D.u=0 at hv
      have := D.u_pos
      omega
    simpa using hne
  · intro b hb c hc hbc
    subst c
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hb
    have hz : D.internalVariable a=D.vVariable ∨ D.internalVariable a=D.xVariable := by simpa using hc
    rcases hz with hz|hz
    · have h := congrArg Subtype.val hz
      have := D.a_lt a.val a.property
      change a.val=D.u at h
      omega
    · have h := congrArg Subtype.val hz
      have := D.a_pos a.val a.property
      change a.val=0 at h
      omega

theorem fullVariableList_actions : (D.fullVariableList k).map (fun b => D.fullToG k (MvPolynomial.X b))=
    (D.internalVariableList k).map (fun b => D.internalToG k (MvPolynomial.X b))++D.endpointElements k := by
  simp only [fullVariableList,List.map_append,List.map_map,List.map_cons,List.map_nil]
  congr 1
  · simp only [Function.comp_def,internalToG,AlgHom.comp_apply,internalToFull,MvPolynomial.rename_X]
  · simp only [endpointElements,endpointToG,AlgHom.comp_apply,endpointToFull,MvPolynomial.rename_X]
    rfl

noncomputable instance fullRegularFinite : Module.Finite (D.FullRing k)
    (polynomialRegularModule k D.Variables (D.source.TangentAlgebra k) (D.fullToG k)) := by
  apply regularPresentation_finite
  intro a
  obtain ⟨p,hp⟩ := D.source.fullPolynomialToG_surjective k a
  refine ⟨(D.fullPolynomialEquiv k).symm p,?_⟩
  change D.source.fullPolynomialToG k ((D.fullPolynomialEquiv k) ((D.fullPolynomialEquiv k).symm p))=a
  rw [AlgEquiv.apply_symm_apply,hp]
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.H0Internal; source SHA256 ff9b66eb8a34dec6b90cc5cd6f272879081515da3f4fb4380d7d44a8a4e61570.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def endpointH0Module : ModuleCat (D.InternalRing k) :=
  actionRestrictedH0 (D.endpointElements k) (D.internalToG k).toRingHom

/-- The internal action on native H0 agrees with the action on the
actual quotient QG, with all commuting scalars retained. -/
noncomputable def endpointH0ModuleIso : D.endpointH0Module k ≅ D.QActualModule k :=
  actionRestrictedH0Iso (D.endpointElements k) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective Ideal.mk_ker (D.internalToG k).toRingHom
    (D.internalToQActual k).toRingHom rfl

noncomputable instance endpointH0ModuleFinite : Module.Finite (D.InternalRing k) (D.endpointH0Module k) :=
  Module.Finite.equiv (D.endpointH0ModuleIso k).symm.toLinearEquiv

theorem endpointH0Internal_finite (i : ℕ) : Module.Finite k
    ((actionH0SingleCoefficientComplex k (D.source.TangentAlgebra k) D.a
      (D.endpointElements k) (D.internalToG k) (variableList k D.a)).homology i) := by
  let : Module.Finite (D.InternalRing k)
      (actionRestrictedH0 (D.endpointElements k) (D.internalToG k).toRingHom) := D.endpointH0ModuleFinite k
  exact actionH0Canonical_finite k (D.source.TangentAlgebra k) D.a (D.endpointElements k) (D.internalToG k) i

theorem endpointH0Internal_betti (i : ℕ) : Module.finrank k
    ((actionH0SingleCoefficientComplex k (D.source.TangentAlgebra k) D.a
      (D.endpointElements k) (D.internalToG k) (variableList k D.a)).homology i)=
        totalBetti k D.a (D.QActualModule k) i := by
  let : Module.Finite (D.InternalRing k)
      (actionRestrictedH0 (D.endpointElements k) (D.internalToG k).toRingHom) := D.endpointH0ModuleFinite k
  rw [actionH0Canonical_betti]
  exact totalBetti_iso k D.a (D.endpointH0ModuleIso k) i
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.NativeTransfer; source SHA256 27d310e4152248ab0fd5a05c5d2cc3510832181b2f96a5ff0fc3e38b320afa76.
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory HomologicalComplex NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def fullRegularIso :
    polynomialRegularModule k D.Variables (D.source.TangentAlgebra k) (D.fullToG k) ≅ D.fullG k := by
  let e : polynomialRegularModule k D.Variables (D.source.TangentAlgebra k) (D.fullToG k) ≃ₗ[D.FullRing k] D.fullG k :=
    {toFun a := a
     invFun a := a
     left_inv _ := rfl
     right_inv _ := rfl
     map_add' _ _ := rfl
     map_smul' _ _ := rfl}
  exact e.toModuleIso

noncomputable def endpointExtendedComplex : ChainComplex (ModuleCat k) ℕ :=
  regularExtendedCoefficientComplex k (D.source.TangentAlgebra k) D.a
    (D.endpointElements k) (D.internalToG k) (D.internalVariableList k)

theorem endpointExtended_betti (i : ℕ) :
    Module.finrank k ((D.endpointExtendedComplex k).homology i)=totalBetti k D.Variables (D.fullG k) i :=
  (regularExtendedPolynomialBetti (D.source.TangentAlgebra k) k D.a D.Variables
    (D.endpointElements k) (D.internalToG k) (D.internalVariableList k)
    (D.fullToG k) (D.fullVariableList k) (D.fullVariableList_actions k)
    (D.fullVariableList_mem k) (D.fullVariableList_nodup k) i).trans
      (totalBetti_iso k D.Variables (D.fullRegularIso k) i)

/-- Guards retain the actual H0 row and prevent Nat negative-index
truncation from introducing spurious higher-homology contributions. -/
noncomputable def endpointRemainder (i : ℕ) : ℕ :=
  (if 1 ≤ i then (D.actualP k+D.actualR k)*D.q.choose (i-1) else 0)+
    (if 2 ≤ i then D.actualR k*D.q.choose (i-2) else 0)

theorem endpoint_binomial_correction (i : ℕ) :
    binomialTransform D.q (fun j => if j=0 then 0 else
      Module.finrank k ((D.endpointComplex k).homology j)) i=D.endpointRemainder k i := by
  have he (j : ℕ) : (if j=0 then 0 else Module.finrank k ((D.endpointComplex k).homology j))=
      (if j=1 then D.actualP k+D.actualR k else 0)+(if j=2 then D.actualR k else 0) := by
    by_cases hj0 : j=0
    · simp [hj0]
    by_cases hj1 : j=1
    · subst j
      simpa using D.actualH1_dimension k
    by_cases hj2 : j=2
    · subst j
      simp [actualR]
    · simp only [hj0,hj1,hj2,ite_false,add_zero]
      exact D.endpointHomology_above k j (by omega)
  unfold binomialTransform
  simp_rw [he,mul_add,mul_ite,mul_zero]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_range]
  unfold endpointRemainder
  congr 1 <;> split_ifs <;> first | omega | ac_rfl

/-- Actual double-Koszul comparison for the same G, same endpoints,
and same internal action. All Betti rows, arbitrary original field. -/
theorem actual_native_endpoint_bound (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤
    totalBetti k D.a (D.QActualModule k) i+D.endpointRemainder k i := by
  let : ∀ j,Module.Finite k ((regularPartialCoefficientComplex k (D.source.TangentAlgebra k)
      (D.endpointElements k)).homology j) := fun j => D.endpointHomologyFinite k j
  have h := regularCorrectedComparison k (D.source.TangentAlgebra k) D.a
    (D.endpointElements k) (D.internalToG k) (D.internalVariableList k)
    (D.endpointH0Internal_finite k) i
  rw [D.internalVariableList_length] at h
  change Module.finrank k ((D.endpointExtendedComplex k).homology i)≤
    Module.finrank k ((actionH0SingleCoefficientComplex k (D.source.TangentAlgebra k) D.a
      (D.endpointElements k) (D.internalToG k) (variableList k D.a)).homology i)+
      binomialTransform D.q (fun j => if j=0 then 0 else Module.finrank k ((D.endpointComplex k).homology j)) i at h
  rw [D.endpointH0Internal_betti,D.endpointExtended_betti,D.endpoint_binomial_correction] at h
  exact h
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.AssemblyCoefficients; source SHA256 c56a16daa5ec3baf27b918df04848ee5d3815ed5461b4fbfe278d55ccb60a1f9.
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

theorem fiberPolynomialPoint_injective : Function.Injective
    (fun b : D.FiberBasisIndex => D.fiberPolynomialPoint b.1 b.2) :=
  (D.fiberPolynomialIndexEquiv).injective

/-- Coefficient extraction in the actual E-module assembly. Distinct
residues and distinct monomials cannot cancel after assembly. -/
theorem coreFiberLinearAssembly_coeff (f : ⨁ r : Fin D.u,D.coreFiberIdeal k r)
    (b : D.FiberBasisIndex) :
    (D.coreFiberLinearAssembly k f).coeff (D.fiberPolynomialPoint b.1 b.2)=
      (f b.1).val.coeff b.2.val := by
  let l1 : (⨁ r : Fin D.u,D.coreFiberIdeal k r) →ₗ[k] k :=
    (Finsupp.lapply (D.fiberPolynomialPoint b.1 b.2)).comp
      ((AddMonoidAlgebra.coeffLinearEquiv k).toLinearMap.comp (D.coreFiberLinearAssembly k).toLinearMap)
  let l2 : (⨁ r : Fin D.u,D.coreFiberIdeal k r) →ₗ[k] k :=
    {toFun := fun f => (f b.1).val.coeff b.2.val
     map_add' := by intro x y;change (x b.1+y b.1).val.coeff b.2.val=_;simp
     map_smul' := by intro c x;change (c • x b.1).val.coeff b.2.val=_;simp}
  have he : l1=l2 := by
    apply (D.coreSumBasis k).ext
    rintro ⟨r,a⟩
    change (D.coreFiberLinearAssembly k (D.coreSumBasis k ⟨r,a⟩)).coeff _=_
    rw [D.coreFiberLinearAssembly_basis]
    change (AddMonoidAlgebra.single (D.fiberPolynomialPoint r a) (1:k)).coeff _=_
    rw [AddMonoidAlgebra.coeff_single,Finsupp.single_apply]
    change (if D.fiberPolynomialPoint r a=D.fiberPolynomialPoint b.1 b.2 then (1:k) else 0)=
      ((D.coreSumBasis k ⟨r,a⟩) b.1).val.coeff b.2.val
    rw [D.coreSumBasis_apply]
    by_cases hr : r=b.1
    · subst r
      simp only [DFinsupp.single_eq_same,D.coreFiberBasis_val,MvPolynomial.coeff_monomial]
      congr 1
      apply propext
      constructor
      · intro h
        have hh := D.fiberPolynomialIndexEquiv.injective (show D.fiberPolynomialIndexEquiv ⟨b.1,a⟩=D.fiberPolynomialIndexEquiv b from h)
        exact congrArg (fun a : {a : Fin 2 →₀ ℕ // (a 0,a 1)∈D.coreFiber b.1} => a.val)
          (eq_of_heq (Sigma.mk.inj_iff.mp hh).2)
      · intro h
        have ha : a=b.2 := Subtype.ext h
        rw [ha]
    · have hne : D.fiberPolynomialPoint r a≠D.fiberPolynomialPoint b.1 b.2 := by
        intro h
        exact hr (congrArg Sigma.fst (D.fiberPolynomialIndexEquiv.injective
          (show D.fiberPolynomialIndexEquiv ⟨r,a⟩=D.fiberPolynomialIndexEquiv b from h)))
      simp only [hne,ite_false,DFinsupp.single_eq_of_ne (Ne.symm hr),ZeroMemClass.coe_zero,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply]
  exact LinearMap.congr_fun he f
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.AssembledKernel; source SHA256 2fb1b13a189b104fd46c73ae56b6a5f3a46010ac148f05eed7d7b9795d6753ce.
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

theorem coreToG_zero_iff (f : D.Core k) : D.coreToG k f=0 ↔
    ∀ p : D.corePoints,¬D.coreDegree p<D.source.order (D.coreValue p).val → f.coeff p=0 := by
  change f∈(D.coreToG k).toLinearMap.ker ↔ _
  rw [D.coreToG_kernel_span]
  change f∈Submodule.span k ((fun p => AddMonoidAlgebra.single p (1:k)) '' _) ↔ _
  rw [←AddMonoidAlgebra.supported_eq_span_single,AddMonoidAlgebra.mem_supported']
  rfl

/-- The E-linear assembly has exactly the independently defined actual
N_r in each component, not the whole forbidden ideal T_r. -/
theorem assembled_kernel_iff (f : ⨁ r : Fin D.u,D.coreFiberIdeal k r) :
    D.coreToG k (D.coreFiberLinearAssembly k f)=0 ↔
      ∀ r,(f r).val∈D.actualKernelIdeal k r := by
  rw [D.coreToG_zero_iff]
  constructor
  · intro h r
    rw [D.actualKernelIdeal_mem]
    intro β hβ
    have hM := (D.coreFiberIdeal_mem k r (f r).val).mp (f r).property β hβ
    refine ⟨hM,?_⟩
    let b : D.FiberBasisIndex := ⟨r,⟨β,hM⟩⟩
    by_contra hdead
    have hz := h (D.fiberPolynomialPoint b.1 b.2) hdead
    rw [D.coreFiberLinearAssembly_coeff] at hz
    exact (Finsupp.mem_support_iff.mp hβ) hz
  · intro h p hp
    let b := D.fiberPolynomialIndexEquiv.symm p
    have he : D.fiberPolynomialPoint b.1 b.2=p := D.fiberPolynomialIndexEquiv.apply_symm_apply p
    rw [←he,D.coreFiberLinearAssembly_coeff]
    by_contra hne
    have hβ : b.2.val∈(f b.1).val.support := Finsupp.mem_support_iff.mpr hne
    have hd := ((D.actualKernelIdeal_mem k b.1 (f b.1).val).mp (h b.1) b.2.val hβ).2
    apply hp
    rw [←he]
    exact hd
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Quotient; source SHA256 fb32cb8eee7b99a2e0a7a722e18106a4d688e727d8d26f6a89974df63a669133.
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
open CategoryTheory
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def actualKernelSubmodule (r : Fin D.u) :
    Submodule (D.EndpointRing k) (D.coreFiberIdeal k r) :=
  Submodule.comap (D.coreFiberIdeal k r).subtype (D.actualKernelIdeal k r)

abbrev FiberQuotient (r : Fin D.u) := (D.coreFiberIdeal k r) ⧸ D.actualKernelSubmodule k r

noncomputable instance fiberQuotientAddCommGroup (r : Fin D.u) : AddCommGroup (D.FiberQuotient k r) :=
  inferInstanceAs (AddCommGroup ((D.coreFiberIdeal k r) ⧸ D.actualKernelSubmodule k r))

noncomputable instance fiberQuotientModuleStructure (r : Fin D.u) : Module (D.EndpointRing k) (D.FiberQuotient k r) :=
  inferInstanceAs (Module (D.EndpointRing k) ((D.coreFiberIdeal k r) ⧸ D.actualKernelSubmodule k r))

noncomputable def fiberQuotientModule : ModuleCat (D.EndpointRing k) :=
  ModuleCat.of (D.EndpointRing k) (⨁ r : Fin D.u,D.FiberQuotient k r)

noncomputable def fiberToG :
    D.fiberSumModule k →ₗ[D.EndpointRing k] D.actualEndpointModule k :=
  (D.coreToGEndpoint k).hom.comp (D.coreFiberModuleEquiv k).symm.toLinearMap

theorem fiberToG_apply (f : ⨁ r : Fin D.u,D.coreFiberIdeal k r) :
    D.fiberToG k f=D.coreToG k (D.coreFiberLinearAssembly k f) := rfl

theorem fiberToG_surjective : Function.Surjective (D.fiberToG k) :=
  (D.coreToGEndpoint_surjective k).comp (D.coreFiberModuleEquiv k).symm.surjective

noncomputable def fiberQuotientMap :
    D.fiberSumModule k →ₗ[D.EndpointRing k] D.fiberQuotientModule k :=
  DFinsupp.mapRange.linearMap (fun r => (D.actualKernelSubmodule k r).mkQ)

theorem fiberQuotientMap_surjective : Function.Surjective (D.fiberQuotientMap k) :=
  (DFinsupp.mapRange_surjective _ (fun r => (D.actualKernelSubmodule k r).mkQ.map_zero)).mpr (fun r => (D.actualKernelSubmodule k r).mkQ_surjective)

theorem fiberToG_kernel : (D.fiberToG k).ker=(D.fiberQuotientMap k).ker := by
  ext f
  change D.fiberToG k f=0 ↔ D.fiberQuotientMap k f=0
  rw [D.fiberToG_apply,D.assembled_kernel_iff]
  constructor
  · intro h
    apply DFinsupp.ext
    intro r
    change (D.actualKernelSubmodule k r).mkQ ((show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from f) r)=0
    exact (Submodule.Quotient.mk_eq_zero _).mpr (h r)
  · intro h r
    have hr := congrArg (fun f : D.fiberQuotientModule k => (show (⨁ r : Fin D.u,D.FiberQuotient k r) from f) r) h
    change (D.actualKernelSubmodule k r).mkQ ((show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from f) r)=0 at hr
    change (show (⨁ r : Fin D.u,D.coreFiberIdeal k r) from f) r∈D.actualKernelSubmodule k r
    exact (Submodule.Quotient.mk_eq_zero (D.actualKernelSubmodule k r)).mp hr

noncomputable def fiberToGQuotientEquiv :
    ((D.fiberSumModule k) ⧸ (D.fiberToG k).ker) ≃ₗ[D.EndpointRing k]
      D.actualEndpointModule k :=
  (D.fiberToG k).quotKerEquivOfSurjective (D.fiberToG_surjective k)

noncomputable def fiberKernelQuotientEquiv :
    ((D.fiberSumModule k) ⧸ (D.fiberToG k).ker) ≃ₗ[D.EndpointRing k]
      ((D.fiberSumModule k) ⧸ (D.fiberQuotientMap k).ker) :=
  Submodule.quotEquivOfEq (D.fiberToG k).ker (D.fiberQuotientMap k).ker (D.fiberToG_kernel k)

noncomputable def fiberQuotientAssemblyEquiv :
    ((D.fiberSumModule k) ⧸ (D.fiberQuotientMap k).ker) ≃ₗ[D.EndpointRing k]
      D.fiberQuotientModule k :=
  (D.fiberQuotientMap k).quotKerEquivOfSurjective (D.fiberQuotientMap_surjective k)

/-- The quotient pieces are the actual M_r/(M_r intersect T_r), and
this equivalence is for the same endpoint action on the same G. -/
noncomputable def actualFiberModuleEquiv :
    D.actualEndpointModule k ≃ₗ[D.EndpointRing k] D.fiberQuotientModule k :=
  (D.fiberToGQuotientEquiv k).symm.trans
    ((D.fiberKernelQuotientEquiv k).trans (D.fiberQuotientAssemblyEquiv k))

theorem actualFiberModuleEquiv_apply (f : ⨁ r : Fin D.u,D.coreFiberIdeal k r) :
    D.actualFiberModuleEquiv k (D.fiberToG k f)=D.fiberQuotientMap k f := by
  simp only [actualFiberModuleEquiv,fiberToGQuotientEquiv,fiberKernelQuotientEquiv,
    fiberQuotientAssemblyEquiv,LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotEquivOfEq_mk,LinearMap.quotKerEquivOfSurjective_apply_mk]
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CoreWords; source SHA256 be6221923ed19d28cfd03e827adcb95b2edeb59fd4301eb0658b113928de34c7.

namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

def coreWord (w : List D.Variables) : D.corePoints := (w.map D.coreGeneratorPoint).sum

@[simp] theorem coreWord_nil : D.coreWord []=0 := rfl

theorem coreWord_cons (b : D.Variables) (w : List D.Variables) :
    D.coreWord (b::w)=D.coreGeneratorPoint b+D.coreWord w := rfl

theorem coreWord_append (w z : List D.Variables) : D.coreWord (w++z)=D.coreWord w+D.coreWord z := by
  simp only [coreWord,List.map_append,List.sum_append]

theorem coreWord_degree (w : List D.Variables) : D.coreDegree (D.coreWord w)=w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [D.coreWord_cons,(D.coreDegree).map_add]
    change 1+D.coreDegree (D.coreWord w)=List.length (b::w)
    rw [ih,List.length_cons]
    omega

theorem coreWord_offset (w : List D.Variables) : D.coreOffset (D.coreWord w)=(w.map Subtype.val).sum := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [D.coreWord_cons,(D.coreOffset).map_add]
    change b.val+D.coreOffset (D.coreWord w)=b.val+(w.map Subtype.val).sum
    rw [ih]

/-- Closure membership supplies a genuine word in the same generator
monoid, not merely a degree/offset bound. -/
theorem exists_coreWord (p : D.corePoints) : ∃ w : List D.Variables,D.coreWord w=p := by
  have h : ∃ w : List D.Variables,(D.coreWord w).val=p.val := by
    apply AddSubmonoid.closure_induction (motive:=fun a _ => ∃ w : List D.Variables,(D.coreWord w).val=a) ?_ ?_ ?_ p.property
    · rintro a ⟨b,rfl⟩
      exact ⟨[b],by simp only [coreWord,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero];rfl⟩
    · exact ⟨[],rfl⟩
    · rintro a b _ _ ⟨w,hw⟩ ⟨z,hz⟩
      refine ⟨w++z,?_⟩
      rw [D.coreWord_append]
      change (D.coreWord w).val+(D.coreWord z).val=a+b
      rw [hw,hz]
  obtain ⟨w,hw⟩ := h
  exact ⟨w,Subtype.ext hw⟩
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Minimal; source SHA256 451f25bcda1520057a839f47e4b92773a9364e35473c68cbcae1adfe3fc36956.
set_option backward.isDefEq.respectTransparency false
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem coreCoordinates_add_endpoint (p : D.corePoints) (c : ℕ×ℕ) :
    D.coreCoordinates (p+D.coreEndpointPoint c)=
      ((D.coreCoordinates p).1,(D.coreCoordinates p).2.1+c.1,(D.coreCoordinates p).2.2+c.2) := by
  apply D.decodeCoordinate_injective
  rw [D.decode_coreCoordinates]
  change p.val+(D.coreEndpointPoint c).val=_
  rw [← D.decode_coreCoordinates p,D.coreEndpointPoint_coe]
  apply Prod.ext
  · dsimp [decodeCoordinate];ring
  · dsimp [decodeCoordinate];ring

theorem exists_minimalFiber_le (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    ∃ b≤c,Minimal (·∈D.coreFiber r) b :=
  exists_minimal_le_of_wellFoundedLT (·∈D.coreFiber r) c hc

theorem coordinate_mem_fiber (p : D.corePoints) :
    (D.coreCoordinates p).2∈D.coreFiber (D.coreCoordinates p).1 :=
  (D.coreCoordinateEquiv p).property

/-- A genuine minimal fiber monomial has no nonconstant endpoint
factor, including factors consisting only of x or only of v. -/
theorem minimal_endpoint_factor (p q : D.corePoints) (c : ℕ×ℕ)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates p).1) (D.coreCoordinates p).2)
    (h : p=q+D.coreEndpointPoint c) : c=0 := by
  have hc := D.coreCoordinates_add_endpoint q c
  rw [← h] at hc
  have hr := congrArg (fun a : D.Coordinate => a.1) hc
  change (D.coreCoordinates p).1=(D.coreCoordinates q).1 at hr
  have hM := D.coordinate_mem_fiber q
  rw [← hr] at hM
  have h1 : (D.coreCoordinates p).2.1=(D.coreCoordinates q).2.1+c.1 :=
    congrArg (fun a : D.Coordinate => a.2.1) hc
  have h2 : (D.coreCoordinates p).2.2=(D.coreCoordinates q).2.2+c.2 :=
    congrArg (fun a : D.Coordinate => a.2.2) hc
  have hle : (D.coreCoordinates q).2≤(D.coreCoordinates p).2 := ⟨by omega,by omega⟩
  have he := hmin.eq_of_le hM hle
  have he1 := congrArg Prod.fst he
  have he2 := congrArg Prod.snd he
  apply Prod.ext
  · change c.1=0
    omega
  · change c.2=0
    omega
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.MinimalWords; source SHA256 1e31702101044849e7e627199c4279b7fad545bc61c23cb2a78c9cb466c2bb86.
set_option backward.isDefEq.respectTransparency false
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem minimal_word_zero_segment (w0 w1 w2 : List D.Variables)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord (w0++(w1++w2)))).1)
      (D.coreCoordinates (D.coreWord (w0++(w1++w2)))).2)
    (hdiv : D.u∣D.coreOffset (D.coreWord w1)) : w1.length=0 := by
  let n := D.coreDegree (D.coreWord w1)
  let B := D.coreOffset (D.coreWord w1)
  let k := B/D.u
  have hB := D.corePoint_bound (D.coreWord w1).property
  change B≤D.u*n at hB
  have hkB : k*D.u=B := Nat.div_mul_cancel hdiv
  have hk : k≤n := by
    by_contra h
    have hnk : n+1≤k := by omega
    have hmul := Nat.mul_le_mul_left D.u hnk
    have hu := D.u_pos
    nlinarith
  have hpt : D.coreEndpointPoint (n-k,k)=D.coreWord w1 := by
    apply Subtype.ext
    rw [D.coreEndpointPoint_coe]
    apply Prod.ext
    · change n-k+k=n
      exact Nat.sub_add_cancel hk
    · change D.u*k=B
      nlinarith only [hkB]
  have hfac : D.coreWord (w0++(w1++w2))=
      D.coreWord (w0++w2)+D.coreEndpointPoint (n-k,k) := by
    rw [hpt]
    simp only [D.coreWord_append]
    abel
  have hz := D.minimal_endpoint_factor _ _ _ hmin hfac
  have hsum := congrArg (fun c : ℕ×ℕ => c.1+c.2) hz
  change n-k+k=0 at hsum
  have hn : n=0 := by omega
  have hlen := D.coreWord_degree w1
  change n=w1.length at hlen
  omega

/-- Equal prefix residues delete a genuine nonempty endpoint factor;
minimality forces the two prefix positions to coincide. -/
theorem minimal_prefix_eq (w : List D.Variables) (i j : ℕ) (hij : i≤j) (hj : j≤w.length)
    (hmod : D.coreOffset (D.coreWord (w.take i))%D.u=
      D.coreOffset (D.coreWord (w.take j))%D.u)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2) : i=j := by
  let a := w.take i
  let b := (w.drop i).take (j-i)
  let c := w.drop j
  have htake : w.take j=a++b := by
    have h := List.take_add (l:=w) (i:=i) (j:=j-i)
    simpa only [Nat.add_sub_of_le hij] using h
  have htail : b++c=w.drop i := by
    have h := List.take_append_drop (j-i) (w.drop i)
    simpa only [List.drop_drop,Nat.add_sub_of_le hij] using h
  have hw : w=a++(b++c) := by
    rw [htail]
    exact (List.take_append_drop i w).symm
  have hpref : D.coreOffset (D.coreWord (w.take j))=
      D.coreOffset (D.coreWord a)+D.coreOffset (D.coreWord b) := by
    rw [htake,D.coreWord_append,(D.coreOffset).map_add]
  have he : D.coreOffset (D.coreWord a) ≡ D.coreOffset (D.coreWord (w.take j)) [MOD D.u] := hmod
  have hdiv := he.dvd'
  rw [hpref,Nat.add_sub_cancel_left] at hdiv
  have hmin' : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord (a++(b++c)))).1)
      (D.coreCoordinates (D.coreWord (a++(b++c)))).2 := by
    rw [← hw]
    exact hmin
  have hz := D.minimal_word_zero_segment a b c hmin' hdiv
  have hlen : b.length=j-i := by
    dsimp [b]
    rw [List.length_take,List.length_drop]
    exact min_eq_left (by omega)
  omega

def corePrefixResidue (w : List D.Variables) (i : Fin (w.length+1)) : Fin D.u :=
  ⟨D.coreOffset (D.coreWord (w.take i.val))%D.u,Nat.mod_lt _ D.u_pos⟩

theorem minimal_word_prefix_injective (w : List D.Variables)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2) : Function.Injective (D.corePrefixResidue w) := by
  intro i j h
  apply Fin.ext
  have hm := congrArg Fin.val h
  by_cases hij : i.val≤j.val
  · exact D.minimal_prefix_eq w i.val j.val hij (by have := j.isLt;omega) hm hmin
  · exact (D.minimal_prefix_eq w j.val i.val (by omega) (by have := i.isLt;omega) hm.symm hmin).symm

theorem minimal_word_length_lt (w : List D.Variables)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2) : w.length<D.u := by
  have h := Fintype.card_le_of_injective (D.corePrefixResidue w) (D.minimal_word_prefix_injective w hmin)
  simp only [Fintype.card_fin] at h
  omega
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.OffsetOrder; source SHA256 c8e0accf63cbd7b149a3116c9af3ebe9f31d730c56bd959696cba28e5b2f9eda.

namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem q_add_one_le_u : D.q+1≤D.u := by
  have hs : D.offsets⊆Finset.range (D.u+1) := by
    intro b hb
    apply Finset.mem_range.mpr
    have := D.offset_le hb
    omega
  have h := Finset.card_le_card hs
  rw [D.offsets_card,Finset.card_range] at h
  omega

noncomputable def internalOffset : Fin D.q → ℕ := D.a.orderEmbOfFin rfl

theorem internalOffset_strictMono : StrictMono D.internalOffset := (D.a.orderEmbOfFin rfl).strictMono

theorem internalOffset_mem (i : Fin D.q) : D.internalOffset i∈D.a := Finset.orderEmbOfFin_mem _ _ i

theorem internalOffset_pos (i : Fin D.q) : 0 < D.internalOffset i := D.a_pos _ (D.internalOffset_mem i)

theorem internalOffset_lt (i : Fin D.q) : D.internalOffset i<D.u := D.a_lt _ (D.internalOffset_mem i)
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.MinimalBounds; source SHA256 67b62ff04a5b4c4dcafe796b3b8e9d3c9954b8ddb6a51eb8bf57d7662fe898f3.
set_option backward.isDefEq.respectTransparency false
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem coreCoordinates_decode (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    D.coreCoordinates ⟨D.decodeCoordinate (r,c),hc⟩=(r,c) := by
  apply D.decodeCoordinate_injective
  exact D.decode_coreCoordinates _

theorem minimalFiber_degree_lt (r : Fin D.u) (c : ℕ×ℕ)
    (h : Minimal (·∈D.coreFiber r) c) : c.1+c.2+D.epsilon r<D.u := by
  let p : D.corePoints := ⟨D.decodeCoordinate (r,c),h.prop⟩
  obtain ⟨w,hw⟩ := D.exists_coreWord p
  have hc := D.coreCoordinates_decode r c h.prop
  change D.coreCoordinates p=(r,c) at hc
  have hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2 := by rw [hw,hc];exact h
  have hb := D.minimal_word_length_lt w hmin
  have hd := D.coreWord_degree w
  rw [hw] at hd
  change c.1+c.2+D.epsilon r=w.length at hd
  omega

theorem minimalFiber_zero (c : ℕ×ℕ) (h : Minimal (·∈D.coreFiber ⟨0,D.u_pos⟩) c) : c=0 := by
  exact (h.eq_of_le (D.coreFiber_zero (0,0)) bot_le).symm

/-- The exceptional residue zero is the unit ideal; all other minimal
points have epsilon one, so every minimal L+K is at most u-2. -/
theorem minimalFiber_budget (r : Fin D.u) (c : ℕ×ℕ)
    (h : Minimal (·∈D.coreFiber r) c) : c.1+c.2≤D.u-2 := by
  by_cases hr : r.val=0
  · have he : r=⟨0,D.u_pos⟩ := Fin.ext hr
    subst r
    rw [D.minimalFiber_zero c h]
    simp only [Prod.fst_zero,Prod.snd_zero,add_zero,Nat.zero_le]
  · have hb := D.minimalFiber_degree_lt r c h
    have he : D.epsilon r=1 := by simp only [epsilon,hr,ite_false]
    rw [he] at hb
    omega

theorem minimalFiber_finite (r : Fin D.u) : Set.Finite {c | Minimal (·∈D.coreFiber r) c} := by
  apply (Set.finite_Iic (D.u-2,D.u-2)).subset
  intro c hc
  have hb := D.minimalFiber_budget r c hc
  exact ⟨by omega,by omega⟩

/-- Minimal words use only the actual internal offsets. Endpoint
letters are excluded by deleting their singleton zero-residue segment. -/
theorem minimal_word_internal (w : List D.Variables)
    (hmin : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2) : ∀ b∈w,b.val∈D.a := by
  intro b hb
  rcases (D.mem_offsets b.val).mp b.property with h0|hu|ha
  · obtain ⟨l,z,hw⟩ := List.mem_iff_append.mp hb
    have hmin' : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord (l++([b]++z)))).1)
        (D.coreCoordinates (D.coreWord (l++([b]++z)))).2 := by simpa only [List.singleton_append,←hw] using hmin
    have hh := D.minimal_word_zero_segment l [b] z hmin' (by
      change D.u∣b.val
      rw [h0]
      exact dvd_zero _)
    simp only [List.length_singleton] at hh
    omega
  · obtain ⟨l,z,hw⟩ := List.mem_iff_append.mp hb
    have hmin' : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord (l++([b]++z)))).1)
        (D.coreCoordinates (D.coreWord (l++([b]++z)))).2 := by simpa only [List.singleton_append,←hw] using hmin
    have hh := D.minimal_word_zero_segment l [b] z hmin' (by
      change D.u∣b.val
      rw [hu])
    simp only [List.length_singleton] at hh
    omega
  · exact ha

/-- A finite, pure internal, bounded-length representation is derived
for every actual minimal fiber point. -/
theorem exists_minimal_internal_word (r : Fin D.u) (c : ℕ×ℕ)
    (h : Minimal (·∈D.coreFiber r) c) :
    ∃ w : List D.Variables,D.coreCoordinates (D.coreWord w)=(r,c) ∧
      w.length≤D.u-1 ∧ ∀ b∈w,b.val∈D.a := by
  let p : D.corePoints := ⟨D.decodeCoordinate (r,c),h.prop⟩
  obtain ⟨w,hw⟩ := D.exists_coreWord p
  have hc := D.coreCoordinates_decode r c h.prop
  change D.coreCoordinates p=(r,c) at hc
  have hm : Minimal (·∈D.coreFiber (D.coreCoordinates (D.coreWord w)).1)
      (D.coreCoordinates (D.coreWord w)).2 := by rw [hw,hc];exact h
  exact ⟨w,by rw [hw,hc],by have := D.minimal_word_length_lt w hm;omega,D.minimal_word_internal w hm⟩
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Residues; source SHA256 c9c675e4818bcadcc49079773d79f996e0e34781585e1860fc60a6698f48153e.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem offsets_setGcd : Nat.setGcd (D.offsets : Set ℕ)=1 := by
  apply Nat.dvd_one.mp
  rw [←D.offsets_coprime]
  exact Nat.dvd_gcd (Finset.dvd_gcd (fun b hb =>
    Nat.setGcd_dvd_of_mem (show b∈(D.offsets : Set ℕ) by simp [hb])))
    (Nat.setGcd_dvd_of_mem (show D.u∈(D.offsets : Set ℕ) by simp))

theorem offsetClosure_core {B : ℕ} (h : B∈AddSubmonoid.closure (D.offsets : Set ℕ)) :
    ∃ p : D.corePoints,D.coreOffset p=B := by
  apply AddSubmonoid.closure_induction (motive:=fun B _ => ∃ p : D.corePoints,D.coreOffset p=B) ?_ ?_ ?_ h
  · intro b hb
    exact ⟨D.coreGeneratorPoint ⟨b,hb⟩,rfl⟩
  · exact ⟨0,rfl⟩
  · rintro b c _ _ ⟨p,hp⟩ ⟨q,hq⟩
    exact ⟨p+q,by rw [(D.coreOffset).map_add,hp,hq]⟩

/-- Every residue occurs in the genuine core, using the collective gcd
condition only. No individual internal offset is assumed invertible. -/
theorem coreFiber_nonempty (r : Fin D.u) : ∃ c : ℕ×ℕ,c∈D.coreFiber r := by
  obtain ⟨C,hC⟩ := Nat.exists_mem_closure_of_ge (D.offsets : Set ℕ)
  have hlarge : C≤r.val+D.u*C := by have := D.u_pos;nlinarith
  obtain ⟨p,hp⟩ := D.offsetClosure_core (hC (r.val+D.u*C) hlarge (by rw [D.offsets_setGcd];exact one_dvd _))
  have hr : (D.coreCoordinates p).1=r := by
    apply Fin.ext
    change D.coreOffset p%D.u=r.val
    rw [hp,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt r.isLt]
  exact ⟨(D.coreCoordinates p).2,by rw [←hr];exact D.coordinate_mem_fiber p⟩

theorem exists_residueDegree (r : Fin D.u) : ∃ n,∃ c : ℕ×ℕ,c∈D.coreFiber r ∧
    c.1+c.2+D.epsilon r=n := by
  obtain ⟨c,hc⟩ := D.coreFiber_nonempty r
  exact ⟨_,c,hc,rfl⟩

noncomputable def shortestDegree (r : Fin D.u) : ℕ := Nat.find (D.exists_residueDegree r)
noncomputable def shortestPoint (r : Fin D.u) : ℕ×ℕ := (Nat.find_spec (D.exists_residueDegree r)).choose

theorem shortestPoint_mem (r : Fin D.u) : D.shortestPoint r∈D.coreFiber r :=
  (Nat.find_spec (D.exists_residueDegree r)).choose_spec.1

theorem shortestPoint_degree (r : Fin D.u) :
    (D.shortestPoint r).1+(D.shortestPoint r).2+D.epsilon r=D.shortestDegree r :=
  (Nat.find_spec (D.exists_residueDegree r)).choose_spec.2

theorem shortestDegree_le (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    D.shortestDegree r≤c.1+c.2+D.epsilon r := Nat.find_min' _ ⟨c,hc,rfl⟩

theorem shortestPoint_minimal (r : Fin D.u) : Minimal (·∈D.coreFiber r) (D.shortestPoint r) := by
  constructor
  · exact D.shortestPoint_mem r
  · intro b hb hle
    have hdeg := D.shortestDegree_le r b hb
    have he := D.shortestPoint_degree r
    exact ⟨by have := hle.1;have := hle.2;omega,by have := hle.1;have := hle.2;omega⟩

theorem shortestDegree_lt (r : Fin D.u) : D.shortestDegree r<D.u := by
  rw [←D.shortestPoint_degree r]
  exact D.minimalFiber_degree_lt r _ (D.shortestPoint_minimal r)

theorem shortestDegree_zero : D.shortestDegree ⟨0,D.u_pos⟩=0 := by
  have h := D.shortestDegree_le ⟨0,D.u_pos⟩ (0,0) (D.coreFiber_zero (0,0))
  simpa only [epsilon,ite_true,Nat.zero_add,Nat.le_zero] using h
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.MinimalGenerators; source SHA256 396b85f31a73381d2fd53b063e4fc8ece863207d188816752d209f111cbb705e.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

noncomputable def minimalPoints (r : Fin D.u) : Finset (ℕ×ℕ) := (D.minimalFiber_finite r).toFinset

@[simp] theorem mem_minimalPoints (r : Fin D.u) (c : ℕ×ℕ) :
    c∈D.minimalPoints r ↔ Minimal (·∈D.coreFiber r) c := Set.Finite.mem_toFinset _

noncomputable def coreHeight : ℕ := Finset.univ.sup (fun r : Fin D.u => (D.minimalPoints r).sup Prod.fst)

theorem minimalPoint_height (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.minimalPoints r) : c.1≤D.coreHeight :=
  (Finset.le_sup hc).trans (Finset.le_sup (f:=fun r : Fin D.u => (D.minimalPoints r).sup Prod.fst) (Finset.mem_univ r))

theorem coreHeight_le : D.coreHeight≤D.u-2 := by
  apply Finset.sup_le
  intro r _
  apply Finset.sup_le
  intro c hc
  have h := D.minimalFiber_budget r c ((D.mem_minimalPoints r c).mp hc)
  omega

variable (k : Type) [Field k]

/-- The actual ideal has precisely the minimal bounded internal words
as monomial generators. This is stronger than abstract Noetherianity. -/
theorem coreFiberIdeal_minimal_generators (r : Fin D.u) :
    D.coreFiberIdeal k r=Ideal.span ((fun β : Fin 2 →₀ ℕ => MvPolynomial.monomial β (1:k)) ''
      {β | Minimal (·∈D.coreFiber r) (β 0,β 1)}) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨β,hβ,rfl⟩
    apply MvPolynomial.mem_ideal_span_monomial_image.mpr
    intro γ hγ
    have he : β=γ := by
      by_contra hne
      have hz : (MvPolynomial.monomial β (1:k)).coeff γ=0 := by
        simp only [MvPolynomial.coeff_monomial,hne,ite_false]
      exact (Finsupp.mem_support_iff.mp hγ) hz
    subst γ
    obtain ⟨c,hc,hmin⟩ := D.exists_minimalFiber_le r (β 0,β 1) hβ
    refine ⟨NSP14.Endpoint.exponentPairEquiv c,?_,?_⟩
    · change Minimal (·∈D.coreFiber r) (NSP14.Endpoint.exponentPairEquiv.symm (NSP14.Endpoint.exponentPairEquiv c))
      rw [AddEquiv.symm_apply_apply]
      exact hmin
    · intro i
      fin_cases i <;> simpa [NSP14.Endpoint.exponentPairEquiv] using (by first | exact hc.1 | exact hc.2)
  · apply Ideal.span_le.mpr
    rintro _ ⟨β,hβ,rfl⟩
    exact Ideal.subset_span ⟨β,hβ.prop,rfl⟩

theorem coreFiberIdeal_ne_bot (r : Fin D.u) : D.coreFiberIdeal k r≠⊥ := by
  obtain ⟨c,hc⟩ := D.coreFiber_nonempty r
  let β := NSP14.Endpoint.exponentPairEquiv c
  have hβ : (β 0,β 1)∈D.coreFiber r := by
    change NSP14.Endpoint.exponentPairEquiv.symm (NSP14.Endpoint.exponentPairEquiv c)∈D.coreFiber r
    rw [AddEquiv.symm_apply_apply]
    exact hc
  have hm : MvPolynomial.monomial β (1:k)∈D.coreFiberIdeal k r := Ideal.subset_span ⟨β,hβ,rfl⟩
  intro hz
  rw [hz,Submodule.mem_bot] at hm
  have hcoeff := congrArg (fun f : D.EndpointRing k => f.coeff β) hm
  exact one_ne_zero (by simpa only [MvPolynomial.coeff_monomial,ite_true,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using hcoeff)
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Volume; source SHA256 aac92e28ff1abc9f41096b2cf925fecd82d2154e57ecce0981639f1793f425ee.
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem minimalPoints_card_eq (r : Fin D.u) : (D.minimalPoints r).card=
    Nat.card {c | Minimal (·∈D.coreFiber r) c} := by
  exact (Nat.card_eq_card_finite_toFinset (D.minimalFiber_finite r)).symm

theorem minimalPoints_card_le (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    (D.minimalPoints r).card≤c.1+c.2+1 := by
  rw [D.minimalPoints_card_eq]
  simpa only [Nat.sub_zero] using NSP14.Endpoint.minimal_card_le (D.coreFiber r) c 0 hc (by simp)

theorem minimalPoints_card_zero : (D.minimalPoints ⟨0,D.u_pos⟩).card=1 := by
  have he : D.minimalPoints ⟨0,D.u_pos⟩={(0,0)} := by
    ext c
    rw [D.mem_minimalPoints,Finset.mem_singleton]
    constructor
    · exact D.minimalFiber_zero c
    · intro hc
      subst c
      exact ⟨D.coreFiber_zero (0,0),fun b _ hb => bot_le⟩
  rw [he,Finset.card_singleton]

theorem minimalPoints_shortest_bound (r : Fin D.u) :
    (D.minimalPoints r).card≤D.shortestDegree r+(if r.val=0 then 1 else 0) := by
  by_cases hr : r.val=0
  · have he : r=⟨0,D.u_pos⟩ := Fin.ext hr
    subst r
    rw [D.minimalPoints_card_zero,D.shortestDegree_zero]
    simp
  · have h := D.minimalPoints_card_le r (D.shortestPoint r) (D.shortestPoint_mem r)
    have he := D.shortestPoint_degree r
    simp only [epsilon,hr,ite_false] at he
    simp only [hr,ite_false,add_zero]
    omega

noncomputable def wordVolume : ℕ := 1+∑ r : Fin D.u,D.shortestDegree r
noncomputable def minimalCount : ℕ := ∑ r : Fin D.u,(D.minimalPoints r).card

/-- The shortest path resource controls all actual minimal fiber
points simultaneously. The unit residue contributes the single 1. -/
theorem minimalCount_volume : (∑ r : Fin D.u,(D.minimalPoints r).card)≤
    1+∑ r : Fin D.u,D.shortestDegree r := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun r _ => D.minimalPoints_shortest_bound r)
  rw [Finset.sum_add_distrib] at h
  have he : (∑ r : Fin D.u,if r.val=0 then 1 else 0)=1 := by
    have hh (r : Fin D.u) : r.val=0 ↔ r=⟨0,D.u_pos⟩ := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [he] at h
  omega
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CarrySums; source SHA256 9ae46d0698db6b8222d4f01dddd4348087fff6bc722d2a7b9c863540dce90652.
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem shiftedResidue_one_injective : Function.Injective (fun r : Fin D.u => D.shiftedResidue r 1) := by
  intro r s h
  have hm : r.val+D.m ≡ s.val+D.m [MOD D.u] := by
    change (r.val+D.m)%D.u=(s.val+D.m)%D.u
    have hv := congrArg Fin.val h
    simpa only [shiftedResidue,one_mul] using hv
  have hc := Nat.ModEq.add_right_cancel (show D.m ≡ D.m [MOD D.u] from rfl) hm
  apply Fin.ext
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt r.isLt,Nat.mod_eq_of_lt s.isLt] using hc

noncomputable def shiftOneEquiv : Fin D.u ≃ Fin D.u :=
  Equiv.ofBijective (fun r => D.shiftedResidue r 1)
    ⟨D.shiftedResidue_one_injective,Finite.surjective_of_injective D.shiftedResidue_one_injective⟩

theorem carry_sum_one : (∑ r : Fin D.u,D.carry r 1)=D.m := by
  have he := Finset.sum_congr (s₁:=Finset.univ) rfl (fun r _ => D.carry_eq r 1)
  simp only [one_mul,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,←Finset.mul_sum] at he
  have hp := D.shiftOneEquiv.sum_comp (fun r => r.val)
  change (∑ r : Fin D.u,(D.shiftedResidue r 1).val)=(∑ r : Fin D.u,r.val) at hp
  rw [hp] at he
  apply Nat.eq_of_mul_eq_mul_left D.u_pos
  omega

/-- Natural arithmetic expression for ceil((m-s)/u), with 0<=s<u<m. -/
def residueCeiling (s : Fin D.u) : ℕ := (D.m+D.u-1-s.val)/D.u

theorem residueCeiling_shift (r : Fin D.u) : D.residueCeiling (D.shiftedResidue r 1)=D.carry r 1 := by
  have hc := D.carry_eq r 1
  simp only [one_mul] at hc
  have hr := r.isLt
  have hs := (D.shiftedResidue r 1).isLt
  have hu := D.u_pos
  have hm := D.u_lt
  have hN : D.m+D.u-1-(D.shiftedResidue r 1).val+(D.shiftedResidue r 1).val+1=D.m+D.u := by omega
  unfold residueCeiling
  apply Nat.div_eq_of_lt_le <;> nlinarith

theorem residueCeiling_sum : (∑ s : Fin D.u,D.residueCeiling s)=D.m := by
  rw [←D.shiftOneEquiv.sum_comp (D.residueCeiling)]
  change (∑ r : Fin D.u,D.residueCeiling (D.shiftedResidue r 1))=D.m
  simp_rw [D.residueCeiling_shift]
  exact D.carry_sum_one

theorem epsilon_sum_add_one : (∑ r : Fin D.u,D.epsilon r)+1=D.u := by
  have he (r : Fin D.u) : D.epsilon r+(if r.val=0 then 1 else 0)=1 := by
    unfold epsilon
    split_ifs <;> omega
  have hs := Finset.sum_congr (s₁:=Finset.univ) rfl (fun r _ => he r)
  rw [Finset.sum_add_distrib] at hs
  have hz : (∑ r : Fin D.u,if r.val=0 then 1 else 0)=1 := by
    have hh (r : Fin D.u) : r.val=0 ↔ r=⟨0,D.u_pos⟩ := ⟨fun h => Fin.ext h,fun h => congrArg Fin.val h⟩
    simp only [hh,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simpa only [hz,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one] using hs

theorem wordVolume_coordinates : D.wordVolume=
    (∑ r : Fin D.u,((D.shortestPoint r).1+(D.shortestPoint r).2))+D.u := by
  have hs := Finset.sum_congr (s₁:=Finset.univ) rfl (fun r _ => D.shortestPoint_degree r)
  rw [Finset.sum_add_distrib] at hs
  have he := D.epsilon_sum_add_one
  unfold wordVolume
  rw [←hs]
  omega
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CompetitorBounds; source SHA256 5265a086da0725401d61e5bf53224e1ebc3a05b006be4503bb6b83c62b6c8434.
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem shiftedResidue_u (s : Fin D.u) : D.shiftedResidue s D.u=s := by
  apply Fin.ext
  change (s.val+D.u*D.m)%D.u=s.val
  rw [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt s.isLt]

theorem competitorFiber_nonempty (s : Fin D.u) : ∃ c : ℕ×ℕ,c∈D.competitorFiber s := by
  obtain ⟨c,hc⟩ := D.coreFiber_nonempty s
  exact ⟨D.forbiddenStart s D.u c,s,D.u,D.u_pos,c,hc,D.shiftedResidue_u s,le_rfl⟩

theorem competitorFloor_exists (s : Fin D.u) : ∃ K,∃ c : ℕ×ℕ,c∈D.competitorFiber s ∧ c.2=K := by
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  exact ⟨c.2,c,hc,rfl⟩

noncomputable def competitorFloor (s : Fin D.u) : ℕ := Nat.find (D.competitorFloor_exists s)

theorem competitorFloor_le (s : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.competitorFiber s) :
    D.competitorFloor s≤c.2 := Nat.find_min' _ ⟨c,hc,rfl⟩

theorem competitorMin_finite (s : Fin D.u) : Set.Finite {c | Minimal (·∈D.competitorFiber s) c} := by
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  exact NSP14.Endpoint.minimal_finite_of_mem _ c hc

noncomputable def competitorZ (s : Fin D.u) : ℕ := Nat.card {c | Minimal (·∈D.competitorFiber s) c}-1

theorem competitorMin_card (s : Fin D.u) : Nat.card {c | Minimal (·∈D.competitorFiber s) c}=D.competitorZ s+1 := by
  have : Finite {c | Minimal (·∈D.competitorFiber s) c} := (D.competitorMin_finite s).to_subtype
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  obtain ⟨b,_,hb⟩ := exists_minimal_le_of_wellFoundedLT (·∈D.competitorFiber s) c hc
  have : Nonempty {c | Minimal (·∈D.competitorFiber s) c} := ⟨⟨b,hb⟩⟩
  have hp : 0<Nat.card {c | Minimal (·∈D.competitorFiber s) c} := Nat.card_pos
  unfold competitorZ
  omega

theorem competitorZ_point_bound (s : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.competitorFiber s) :
    D.competitorZ s≤c.1+c.2-D.competitorFloor s := by
  have h := NSP14.Endpoint.minimal_card_le (D.competitorFiber s) c (D.competitorFloor s) hc
    (D.competitorFloor_le s)
  rw [D.competitorMin_card] at h
  omega

theorem competitorMin_height (s : Fin D.u) (c : ℕ×ℕ) (hc : Minimal (·∈D.competitorFiber s) c) :
    c.1≤D.coreHeight-2 := by
  obtain ⟨r,j,hj,a,ha,hs,hstart⟩ := hc.prop
  obtain ⟨b,hba,hb⟩ := D.exists_minimalFiber_le r a ha
  have hstart' : D.forbiddenStart r j b≤c := by
    apply (D.forbiddenStart_le r j b c).mpr
    have h := (D.forbiddenStart_le r j a c).mp hstart
    obtain ⟨hL,hK⟩ := hba
    constructor <;> omega
  have hmem : D.forbiddenStart r j b∈D.competitorFiber s := ⟨r,j,hj,b,hb.prop,hs,le_rfl⟩
  have he := hc.eq_of_le hmem hstart'
  have hh := D.forbiddenStart_height r j b.1 b.2 D.coreHeight
    (D.minimalPoint_height r b ((D.mem_minimalPoints r b).mpr hb))
  change (D.forbiddenStart r j b).1≤D.coreHeight-2*j at hh
  rw [he] at hh
  omega

theorem competitorZ_height (s : Fin D.u) : D.competitorZ s≤D.coreHeight-2 := by
  let f : {c | Minimal (·∈D.competitorFiber s) c} → Fin (D.coreHeight-2+1) :=
    fun c => ⟨c.val.1,by have := D.competitorMin_height s c.val c.property;omega⟩
  have hi : Function.Injective f := by
    intro a b h
    exact Subtype.ext (NSP14.Endpoint.minimal_pair_eq_of_fst a.property b.property (congrArg Fin.val h))
  have hb := Nat.card_le_card_of_injective f hi
  rw [Nat.card_fin,D.competitorMin_card] at hb
  omega

theorem competitor_point_volume (s : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.competitorFiber s) :
    D.m≤s.val+D.u*c.2 := by
  obtain ⟨r,j,hj,b,_,hs,hstart⟩ := hc
  have hK : b.2+D.carry r j≤c.2 := hstart.2
  have hcar := D.carry_eq r j
  rw [hs] at hcar
  have hm := Nat.mul_le_mul_right D.m hj
  nlinarith

theorem competitorFloor_ceiling (s : Fin D.u) : D.residueCeiling s≤D.competitorFloor s := by
  obtain ⟨c,hc,hK⟩ := Nat.find_spec (D.competitorFloor_exists s)
  have hvol := D.competitor_point_volume s c hc
  have hs := s.isLt
  have hm := D.u_lt
  have hu := D.u_pos
  unfold residueCeiling
  apply (Nat.div_le_iff_le_mul hu).mpr
  have hK' : c.2=D.competitorFloor s := hK
  rw [←hK']
  have hvol' : D.m≤s.val+c.2*D.u := by nlinarith only [hvol]
  omega

theorem competitorFloor_sum : D.m≤∑ s : Fin D.u,D.competitorFloor s := by
  rw [←D.residueCeiling_sum]
  exact Finset.sum_le_sum (fun s _ => D.competitorFloor_ceiling s)

theorem competitorZ_shortest (r : Fin D.u) :
    D.competitorZ (D.shiftedResidue r 1)+D.competitorFloor (D.shiftedResidue r 1)≤
      (D.shortestPoint r).1+(D.shortestPoint r).2+D.carry r 1 := by
  let c := D.forbiddenStart r 1 (D.shortestPoint r)
  have hc : c∈D.competitorFiber (D.shiftedResidue r 1) :=
    ⟨r,1,le_rfl,D.shortestPoint r,D.shortestPoint_mem r,rfl,le_rfl⟩
  have hz := D.competitorZ_point_bound _ c hc
  have hK := D.competitorFloor_le _ c hc
  have hL := D.forbiddenStart_height r 1 (D.shortestPoint r).1 (D.shortestPoint r).2
    (D.shortestPoint r).1 le_rfl
  change c.1≤(D.shortestPoint r).1-2*1 at hL
  have hcK : c.2=(D.shortestPoint r).2+D.carry r 1 := rfl
  omega

/-- The same shortest paths, same carries and same T_s are summed.
No reflected or separately optimized data enter this inequality. -/
theorem competitorZ_sum_bound : (∑ s : Fin D.u,D.competitorZ s)≤D.wordVolume-D.u := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun r _ => D.competitorZ_shortest r)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib] at h
  have hz := D.shiftOneEquiv.sum_comp D.competitorZ
  have hκ := D.shiftOneEquiv.sum_comp D.competitorFloor
  change (∑ r : Fin D.u,D.competitorZ (D.shiftedResidue r 1))=(∑ r : Fin D.u,D.competitorZ r) at hz
  change (∑ r : Fin D.u,D.competitorFloor (D.shiftedResidue r 1))=(∑ r : Fin D.u,D.competitorFloor r) at hκ
  rw [hz,hκ,D.carry_sum_one] at h
  have hk := D.competitorFloor_sum
  rw [D.wordVolume_coordinates]
  omega
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.FiberInjection; source SHA256 114150ff14c26bb0893c6dad7c3d2b0b1dad3b3b3ceb0507fd46495cc07818e8.
set_option backward.isDefEq.respectTransparency false
open scoped Classical DirectSum
open CategoryTheory
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

abbrev CompetitorQuotient (s : Fin D.u) := D.EndpointRing k ⧸ D.competitorIdeal k s

noncomputable def fiberToCompetitor (s : Fin D.u) :
    (D.coreFiberIdeal k s) →ₗ[D.EndpointRing k] D.CompetitorQuotient k s :=
  (D.competitorIdeal k s).mkQ.comp (D.coreFiberIdeal k s).subtype

theorem fiberToCompetitor_kernel (s : Fin D.u) :
    (D.fiberToCompetitor k s).ker=D.actualKernelSubmodule k s := by
  ext a
  change Submodule.Quotient.mk a.val=0 ↔ a.val∈D.actualKernelIdeal k s
  rw [Submodule.Quotient.mk_eq_zero,D.actualKernelIdeal_eq_inf,Ideal.mem_inf]
  exact ⟨fun h => ⟨a.property,h⟩,fun h => h.2⟩

noncomputable def fiberCompetitorInjection (s : Fin D.u) :
    D.FiberQuotient k s →ₗ[D.EndpointRing k] D.CompetitorQuotient k s :=
  (D.actualKernelSubmodule k s).liftQ (D.fiberToCompetitor k s)
    (by rw [D.fiberToCompetitor_kernel])

theorem fiberCompetitorInjection_injective (s : Fin D.u) :
    Function.Injective (D.fiberCompetitorInjection k s) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ (by rw [D.fiberToCompetitor_kernel])

noncomputable def fiberCompetitorProductMap : D.fiberQuotientModule k →ₗ[D.EndpointRing k]
    (∀ s : Fin D.u,D.CompetitorQuotient k s) where
  toFun a s := D.fiberCompetitorInjection k s ((show (⨁ s : Fin D.u,D.FiberQuotient k s) from a) s)
  map_add' a b := by ext s;exact (D.fiberCompetitorInjection k s).map_add _ _
  map_smul' p a := by ext s;exact (D.fiberCompetitorInjection k s).map_smul p _

theorem fiberCompetitorProductMap_injective : Function.Injective (D.fiberCompetitorProductMap k) := by
  intro a b h
  apply DFinsupp.ext
  intro s
  exact D.fiberCompetitorInjection_injective k s (congrArg (fun f => f s) h)

/-- The injection uses M/(M intersect T) -> E/T in each component.
No Artin hypothesis is imposed on E/T. -/
noncomputable def actualCompetitorProductInjection : D.actualEndpointModule k →ₗ[D.EndpointRing k]
    (∀ s : Fin D.u,D.CompetitorQuotient k s) :=
  (D.fiberCompetitorProductMap k).comp (D.actualFiberModuleEquiv k).toLinearMap

theorem actualCompetitorProductInjection_injective : Function.Injective (D.actualCompetitorProductInjection k) :=
  (D.fiberCompetitorProductMap_injective k).comp (D.actualFiberModuleEquiv k).injective
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Socle; source SHA256 4bf1eb5bfd26faf05313ffea58da157141bd0470df7ebf4fcf592e56ddee68e6.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def endpointMultiply (i : Fin 2) : D.source.TangentAlgebra k →ₗ[k] D.source.TangentAlgebra k :=
  (LinearMap.mul k (D.source.TangentAlgebra k)).flip (D.endpointToG k (MvPolynomial.X i))

/-- The actual simultaneous annihilator inside the actual G. -/
noncomputable def actualSocle : Submodule k (D.source.TangentAlgebra k) :=
  (D.endpointMultiply k 0).ker⊓(D.endpointMultiply k 1).ker

noncomputable def nativeSocle : Submodule (D.source.TangentAlgebra k) (D.source.TangentAlgebra k) :=
  (D.endpointToG k (MvPolynomial.X 0) •
    𝟙 (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).hom.ker⊓
  (D.endpointToG k (MvPolynomial.X 1) •
    𝟙 (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).hom.ker

noncomputable def nativeSocleCoefficients : ModuleCat k :=
  (ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).obj
    (ModuleCat.of (D.source.TangentAlgebra k) (D.nativeSocle k))

noncomputable def socleCoefficientEquiv : D.nativeSocleCoefficients k ≃ₗ[k] D.actualSocle k where
  toFun a := ⟨a.val,by
    have ha0 : D.endpointToG k (MvPolynomial.X 0)*a.val=0 := a.property.1
    have ha1 : D.endpointToG k (MvPolynomial.X 1)*a.val=0 := a.property.2
    exact ⟨by change a.val*D.endpointToG k (MvPolynomial.X 0)=0;rw [mul_comm];exact ha0,
      by change a.val*D.endpointToG k (MvPolynomial.X 1)=0;rw [mul_comm];exact ha1⟩⟩
  invFun a := ⟨a.val,by
    have ha0 : a.val*D.endpointToG k (MvPolynomial.X 0)=0 := a.property.1
    have ha1 : a.val*D.endpointToG k (MvPolynomial.X 1)=0 := a.property.2
    exact ⟨by change D.endpointToG k (MvPolynomial.X 0)*a.val=0;rw [mul_comm];exact ha0,
      by change D.endpointToG k (MvPolynomial.X 1)*a.val=0;rw [mul_comm];exact ha1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c a := by
    apply Subtype.ext
    change (algebraMap k (D.source.TangentAlgebra k) c)*a.val=c • a.val
    exact (Algebra.smul_def c a.val).symm

/-- The true endpoint H2 is the simultaneous actual annihilator.
The native comparison is G-linear before coefficient restriction. -/
noncomputable def actualH2SocleEquiv : (D.endpointComplex k).homology 2 ≃ₗ[k] D.actualSocle k :=
  (nativeCoefficientHomologyIso k (D.source.TangentAlgebra k)
    (actionRegularComplex (D.source.TangentAlgebra k) (D.endpointElements k)) 2).toLinearEquiv.trans
    (((ModuleCat.restrictScalars (algebraMap k (D.source.TangentAlgebra k))).mapIso
      (NSP14.Endpoint.twoActionH2Equiv (D.source.TangentAlgebra k)
        (D.endpointToG k (MvPolynomial.X 0)) (D.endpointToG k (MvPolynomial.X 1))
        (ModuleCat.of (D.source.TangentAlgebra k) (D.source.TangentAlgebra k))).toModuleIso).toLinearEquiv.trans
      (D.socleCoefficientEquiv k))

noncomputable instance actualSocleFinite : Module.Finite k (D.actualSocle k) :=
  Module.Finite.equiv (D.actualH2SocleEquiv k)

theorem actualR_socle_dimension : D.actualR k=Module.finrank k (D.actualSocle k) :=
  (D.actualH2SocleEquiv k).finrank_eq
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.SocleInjection; source SHA256 530ed62a7f5ba4235a92a52e9db22c2dfc2e381175135e6266923425b21223ed.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

theorem actualSocle_endpoint_zero (a : D.actualSocle k) (i : Fin 2) :
    (MvPolynomial.X i : D.EndpointRing k) • (show D.actualEndpointModule k from a.val)=0 := by
  change D.endpointToG k (MvPolynomial.X i)*a.val=0
  fin_cases i
  · have h : a.val*D.endpointToG k (MvPolynomial.X 0)=0 := a.property.1
    rw [mul_comm]
    exact h
  · have h : a.val*D.endpointToG k (MvPolynomial.X 1)=0 := a.property.2
    rw [mul_comm]
    exact h

theorem actualSocle_competitor_member (a : D.actualSocle k) (s : Fin D.u) :
    D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s∈
      NSP14.Endpoint.coordinateSocle k (D.competitorFiber s) := by
  have he (i : Fin 2) := (D.actualCompetitorProductInjection k).map_smul
    (MvPolynomial.X i : D.EndpointRing k) (show D.actualEndpointModule k from a.val)
  have hz (i : Fin 2) :
      (MvPolynomial.X i : D.EndpointRing k) • D.actualCompetitorProductInjection k
        (show D.actualEndpointModule k from a.val) s=0 := by
    have h := he i
    rw [D.actualSocle_endpoint_zero k a i,map_zero] at h
    exact (congrArg (fun f => f s) h).symm
  constructor
  · have h := hz 0
    change Ideal.Quotient.mk (D.competitorIdeal k s) (MvPolynomial.X (0:Fin 2))*
      D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s=0 at h
    change D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s*
      Ideal.Quotient.mk (D.competitorIdeal k s) (MvPolynomial.X (0:Fin 2))=0
    rw [mul_comm]
    exact h
  · have h := hz 1
    change Ideal.Quotient.mk (D.competitorIdeal k s) (MvPolynomial.X (1:Fin 2))*
      D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s=0 at h
    change D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s*
      Ideal.Quotient.mk (D.competitorIdeal k s) (MvPolynomial.X (1:Fin 2))=0
    rw [mul_comm]
    exact h

/-- Restriction of the actual E-linear injection to actual endpoint
socles, landing in genuine monomial quotient socles. -/
noncomputable def actualSocleProductMap : D.actualSocle k →ₗ[k]
    (∀ s : Fin D.u,NSP14.Endpoint.coordinateSocle k (D.competitorFiber s)) where
  toFun a s := ⟨D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s,
    D.actualSocle_competitor_member k a s⟩
  map_add' a b := by
    ext s
    exact congrArg (fun f => f s) ((D.actualCompetitorProductInjection k).map_add
      (show D.actualEndpointModule k from a.val) (show D.actualEndpointModule k from b.val))
  map_smul' c a := by
    ext s
    change D.actualCompetitorProductInjection k (show D.actualEndpointModule k from c • a.val) s=
      c • D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s
    have h := (D.actualCompetitorProductInjection k).map_smul (MvPolynomial.C c)
      (show D.actualEndpointModule k from a.val)
    have hs : (MvPolynomial.C c : D.EndpointRing k) • (show D.actualEndpointModule k from a.val)=
        (show D.actualEndpointModule k from c • a.val) := by
      change D.endpointToG k (MvPolynomial.C c)*a.val=c • a.val
      have hφ : D.endpointToG k (MvPolynomial.C c)=algebraMap k (D.source.TangentAlgebra k) c := (D.endpointToG k).commutes c
      rw [hφ,Algebra.smul_def]
    rw [hs] at h
    have he := congrArg (fun f => f s) h
    change D.actualCompetitorProductInjection k (show D.actualEndpointModule k from c • a.val) s=
      (MvPolynomial.C c : D.EndpointRing k) • D.actualCompetitorProductInjection k
        (show D.actualEndpointModule k from a.val) s at he
    rw [he]
    change (algebraMap k (D.EndpointRing k) c) •
      (D.actualCompetitorProductInjection k (show D.actualEndpointModule k from a.val) s)=_
    rw [algebraMap_smul]

theorem actualSocleProductMap_injective : Function.Injective (D.actualSocleProductMap k) := by
  intro a b h
  apply Subtype.ext
  apply D.actualCompetitorProductInjection_injective k
  funext s
  exact congrArg (fun f => (f s).val) h
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.Compensation; source SHA256 935daef24217f33f074757c8c6c3b20c5007216b506e596b5d26b35e2076e555.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open CategoryTheory CategoryTheory.Limits NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable instance QCoreCoefficientFinite : Module.Finite k (coefficientModule k D.a (D.QCoreModule k)) :=
  regularRestriction_coefficientFinite k D.a _ _

noncomputable instance QActualCoefficientFinite : Module.Finite k (coefficientModule k D.a (D.QActualModule k)) :=
  regularRestriction_coefficientFinite k D.a _ _

noncomputable def QKernelModule : ModuleCat (D.InternalRing k) :=
  ModuleCat.of (D.InternalRing k) (D.QCoreToActualModule k).hom.ker

noncomputable def QKernelInclusion : D.QKernelModule k ⟶ D.QCoreModule k :=
  ModuleCat.ofHom (X:=D.QKernelModule k) (Y:=D.QCoreModule k) (D.QCoreToActualModule k).hom.ker.subtype

noncomputable def QKernelCoefficientInclusion : coefficientModule k D.a (D.QKernelModule k) ⟶
    coefficientModule k D.a (D.QCoreModule k) :=
  (ModuleCat.restrictScalars (algebraMap k (D.InternalRing k))).map (D.QKernelInclusion k)

theorem QKernelCoefficientInclusion_injective : Function.Injective (D.QKernelCoefficientInclusion k).hom :=
  fun _a _b h => Subtype.ext h

noncomputable instance QKernelCoefficientFinite : Module.Finite k (coefficientModule k D.a (D.QKernelModule k)) :=
  Module.Finite.of_injective (D.QKernelCoefficientInclusion k).hom (D.QKernelCoefficientInclusion_injective k)

noncomputable instance QKernelModuleFinite : Module.Finite (D.InternalRing k) (D.QKernelModule k) :=
  polynomialFinite_of_coefficientFinite _

noncomputable def QKernelSequence : ShortComplex (ModuleCat (D.InternalRing k)) :=
  ShortComplex.mk (D.QKernelInclusion k) (D.QCoreToActualModule k) (by
    apply ModuleCat.hom_ext
    ext a
    exact a.property)

theorem QKernelSequence_shortExact : (D.QKernelSequence k).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact Submodule.range_subtype _
  · rw [ModuleCat.mono_iff_injective]
    exact Subtype.val_injective
  · rw [ModuleCat.epi_iff_surjective]
    exact D.QCoreToActual_surjective k

noncomputable def QCoreCoefficientEquiv : coefficientModule k D.a (D.QCoreModule k) ≃ₗ[k] D.QCore k :=
  regularRestrictionCoefficientEquiv k D.a _ _

noncomputable def QActualCoefficientEquiv : coefficientModule k D.a (D.QActualModule k) ≃ₗ[k] D.QActual k :=
  regularRestrictionCoefficientEquiv k D.a _ _

theorem QKernel_dimension_add :
    Module.finrank k (coefficientModule k D.a (D.QKernelModule k))+D.actualP k=D.coreP k := by
  let S := (D.QKernelSequence k).map (ModuleCat.restrictScalars (algebraMap k (D.InternalRing k)))
  let : Mono (D.QKernelSequence k).f := (D.QKernelSequence_shortExact k).mono_f
  let : Epi (D.QKernelSequence k).g := (D.QKernelSequence_shortExact k).epi_g
  have hS : S.ShortExact := (D.QKernelSequence_shortExact k).map _
  let : Module.Finite k S.X₂ := D.QCoreCoefficientFinite k
  have h := exact_rank_sum k S hS.exact
  have hinj : Function.Injective S.f.hom := D.QKernelCoefficientInclusion_injective k
  have hsurj : Function.Surjective S.g.hom := D.QCoreToActual_surjective k
  rw [LinearMap.finrank_range_of_inj hinj,LinearMap.range_eq_top.mpr hsurj,finrank_top] at h
  change Module.finrank k (coefficientModule k D.a (D.QKernelModule k))+
    Module.finrank k (coefficientModule k D.a (D.QActualModule k))=
      Module.finrank k (coefficientModule k D.a (D.QCoreModule k)) at h
  rw [(D.QCoreCoefficientEquiv k).finrank_eq,(D.QActualCoefficientEquiv k).finrank_eq] at h
  exact h

theorem QKernel_dimension : Module.finrank k (coefficientModule k D.a (D.QKernelModule k))=D.coreP k-D.actualP k := by
  have h := D.QKernel_dimension_add k
  omega

theorem actualP_le_coreP : D.actualP k≤D.coreP k := by
  have h := D.QKernel_dimension_add k
  omega

/-- The compensation is proved using the real quotient and its real
kernel, with the actual LES and finite-k kernel chain bound. -/
theorem actual_kernel_compensation (i : ℕ) : totalBetti k D.a (D.QActualModule k) i≤
    totalBetti k D.a (D.QCoreModule k) i+(if i=0 then 0 else (D.coreP k-D.actualP k)*D.q.choose (i-1)) := by
  cases i with
  | zero =>
    simp only [ite_true,add_zero]
    let : Epi (D.QCoreToActualModule k) := (ModuleCat.epi_iff_surjective _).mpr (D.QCoreToActual_surjective k)
    exact totalBetti_zero_le_of_epi k D.a (D.QCoreToActualModule k)
  | succ i =>
    let : Module.Finite (D.InternalRing k) (D.QKernelSequence k).X₁ := D.QKernelModuleFinite k
    let : Module.Finite (D.InternalRing k) (D.QKernelSequence k).X₂ := D.QCoreModuleFinite k
    let : Module.Finite (D.InternalRing k) (D.QKernelSequence k).X₃ := D.QActualModuleFinite k
    have h := NSP14.Endpoint.quotient_betti_bound k D.a (D.QKernelSequence k) (D.QKernelSequence_shortExact k) i
    change totalBetti k D.a (D.QActualModule k) (i+1)≤
      totalBetti k D.a (D.QCoreModule k) (i+1)+totalBetti k D.a (D.QKernelModule k) i at h
    have hb := NSP14.Endpoint.finite_betti_bound k D.a (D.QKernelModule k) i
    rw [D.QKernel_dimension,Fintype.card_coe] at hb
    change totalBetti k D.a (D.QKernelModule k) i≤(D.coreP k-D.actualP k)*D.q.choose i at hb
    simpa only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel] using
      h.trans (Nat.add_le_add_left hb (totalBetti k D.a (D.QCoreModule k) (i+1)))
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.FullTransfer; source SHA256 dbe038aa0960263c5008666a5f64dd184220af04a907b019baf37139b2f784f1.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def coreRemainder (i : ℕ) : ℕ := if i=0 then 0 else
  D.coreP k*D.q.choose (i-1)+D.actualR k*(D.q+1).choose (i-1)

theorem compensation_merge (i : ℕ) :
    (if i=0 then 0 else (D.coreP k-D.actualP k)*D.q.choose (i-1))+D.endpointRemainder k i=
      D.coreRemainder k i := by
  have hP : D.coreP k-D.actualP k+D.actualP k=D.coreP k := Nat.sub_add_cancel (D.actualP_le_coreP k)
  cases i with
  | zero => simp [endpointRemainder,coreRemainder]
  | succ i =>
    cases i with
    | zero =>
      simp only [Nat.add_sub_cancel,show (0+1:ℕ)≠0 by decide,ite_false,endpointRemainder,
        coreRemainder,show (1:ℕ)≤1 by decide,ite_true,show ¬(2:ℕ)≤1 by decide,
        Nat.choose_zero_right,mul_one,add_zero]
      omega
    | succ i =>
      have hPascal := Nat.choose_succ_succ D.q i
      simp only [endpointRemainder,coreRemainder,show i+1+1≠0 by omega,ite_false,
        show 1 ≤ i+1+1 by omega,show 2 ≤ i+1+1 by omega,ite_true,
        show i+1+1-1=i+1 by omega,show i+1+1-2=i by omega]
      rw [hPascal]
      nlinarith only [congrArg (fun z => z*D.q.choose (i+1)) hP]

/-- Kernel-compensated all-row bound, on the actual full minimal
presentation. The zero row is guarded explicitly. -/
theorem actual_core_endpoint_bound (i : ℕ) : totalBetti k D.Variables (D.fullG k) i≤
    totalBetti k D.a (D.QCoreModule k) i+D.coreRemainder k i := by
  have hn := D.actual_native_endpoint_bound k i
  have hk := D.actual_kernel_compensation k i
  have h := hn.trans (Nat.add_le_add_right hk (D.endpointRemainder k i))
  rw [add_assoc,D.compensation_merge] at h
  exact h

/-- The same bound is exported to the actual completed semigroup
ring tangent cone over the original coefficient field. -/
theorem completed_core_endpoint_bound (i : ℕ) :
    totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i≤
        totalBetti k D.a (D.QCoreModule k) i+D.coreRemainder k i := by
  rw [←D.source.completed_totalBetti k,←D.fullG_totalBetti k]
  exact D.actual_core_endpoint_bound k i

theorem actual_endpoint_top : totalBetti k D.Variables (D.fullG k) (D.q+2)≤D.actualR k := by
  have h := D.actual_core_endpoint_bound k (D.q+2)
  have hb : totalBetti k D.a (D.QCoreModule k) (D.q+2)=0 :=
    totalBetti_eq_zero_of_gt k D.a _ _ (by simp only [Fintype.card_coe];unfold q;omega)
  rw [hb,coreRemainder] at h
  simp only [show D.q+2≠0 by omega,ite_false,show D.q+2-1=D.q+1 by omega,
    Nat.choose_eq_zero_of_lt (show D.q<D.q+1 by omega),mul_zero,Nat.choose_self,mul_one,zero_add] at h
  exact h

theorem actual_endpoint_above (i : ℕ) (hi : D.q+2 < i) : totalBetti k D.Variables (D.fullG k) i=0 :=
  totalBetti_eq_zero_of_gt k D.Variables _ i (by rw [D.variables_card];exact hi)

theorem actual_endpoint_zero : totalBetti k D.Variables (D.fullG k) 0=1 := by
  rw [D.fullG_totalBetti]
  exact D.source.actualG_totalBetti_zero k
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.SocleBounds; source SHA256 229ec4d9a23ae5bc614ba4475f94b26ca6e422b0490faa7431f7d6f352c44613.
set_option backward.isDefEq.respectTransparency false
open scoped Classical BigOperators
open CategoryTheory
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable instance competitorSocleFinite (s : Fin D.u) :
    Module.Finite k (NSP14.Endpoint.coordinateSocle k (D.competitorFiber s)) := by
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  exact NSP14.Endpoint.coordinateSocle_finite k (D.competitorFiber s) (D.competitorFiber_upward s) c hc

theorem competitorSocle_dimension (s : Fin D.u) :
    Module.finrank k (NSP14.Endpoint.coordinateSocle k (D.competitorFiber s))≤D.competitorZ s := by
  obtain ⟨c,hc⟩ := D.competitorFiber_nonempty s
  exact NSP14.Endpoint.coordinateSocle_finrank_bound k (D.competitorFiber s) (D.competitorFiber_upward s) c hc

/-- The real endpoint socle injects into the real T_s quotient socles;
finite-dimensionality is required only for those socles. -/
theorem actualR_le_sum_z : D.actualR k≤∑ s : Fin D.u,D.competitorZ s := by
  let : ∀ s : Fin D.u,Module.Finite k (NSP14.Endpoint.coordinateSocle k (D.competitorFiber s)) :=
    fun s => D.competitorSocleFinite k s
  let : ∀ s : Fin D.u,Module.Free k (NSP14.Endpoint.coordinateSocle k (D.competitorFiber s)) :=
    fun s => Module.Free.of_divisionRing k _
  have h := LinearMap.finrank_le_finrank_of_injective (D.actualSocleProductMap_injective k)
  rw [Module.finrank_pi_fintype] at h
  rw [D.actualR_socle_dimension]
  exact h.trans (Finset.sum_le_sum (fun s _ => D.competitorSocle_dimension k s))

theorem actualR_le_volume : D.actualR k≤D.wordVolume-D.u :=
  (D.actualR_le_sum_z k).trans D.competitorZ_sum_bound

theorem actualR_le_height : D.actualR k≤D.u*(D.coreHeight-2) := by
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun s _ => D.competitorZ_height s)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  exact (D.actualR_le_sum_z k).trans hs

/-- Same-orientation resource: no reflected core is used. Nat subtraction
is max(Hx-2,0); W>=u is proved independently below. -/
noncomputable def Rhat : ℕ := min (D.wordVolume-D.u) (D.u*(D.coreHeight-2))

theorem wordVolume_ge_u : D.u≤D.wordVolume := by
  rw [D.wordVolume_coordinates]
  omega

theorem actualR_le_Rhat : D.actualR k≤D.Rhat :=
  le_min (D.actualR_le_volume k) (D.actualR_le_height k)

noncomputable def coreRhatRemainder (i : ℕ) : ℕ := if i=0 then 0 else
  D.coreP k*D.q.choose (i-1)+D.Rhat*(D.q+1).choose (i-1)

theorem coreRemainder_le_Rhat (i : ℕ) : D.coreRemainder k i≤D.coreRhatRemainder k i := by
  unfold coreRemainder coreRhatRemainder
  split_ifs
  · rfl
  · exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (D.actualR_le_Rhat k)) _

theorem actual_core_Rhat_bound (i : ℕ) :
    NSP14.Homological.totalBetti k D.Variables (D.fullG k) i≤
      NSP14.Homological.totalBetti k D.a (D.QCoreModule k) i+D.coreRhatRemainder k i :=
  (D.actual_core_endpoint_bound k i).trans (Nat.add_le_add_left (D.coreRemainder_le_Rhat k i) _)

theorem completed_core_Rhat_bound (i : ℕ) :
    NSP14.Homological.totalBetti k D.source.AtomExponent
      (ModuleCat.of (D.source.FullPolynomialRing k) (D.source.FormalTangentAlgebra k)) i≤
        NSP14.Homological.totalBetti k D.a (D.QCoreModule k) i+D.coreRhatRemainder k i :=
  (D.completed_core_endpoint_bound k i).trans (Nat.add_le_add_left (D.coreRemainder_le_Rhat k i) _)

theorem actual_endpoint_top_Rhat : NSP14.Homological.totalBetti k D.Variables (D.fullG k) (D.q+2)≤D.Rhat :=
  (D.actual_endpoint_top k).trans (D.actualR_le_Rhat k)
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.MinimalPredecessors; source SHA256 6afd6024d97b602022ba98d07034e7b7525799b2a2b3078bdccc6f1f08ffbf83.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem minimalFiber_iff_predecessors (r : Fin D.u) (c : ℕ×ℕ) (hc : c∈D.coreFiber r) :
    Minimal (·∈D.coreFiber r) c ↔
      (c.1=0 ∨ (c.1-1,c.2)∉D.coreFiber r) ∧ (c.2=0 ∨ (c.1,c.2-1)∉D.coreFiber r) := by
  constructor
  · intro h
    constructor
    · by_cases h0 : c.1=0
      · exact Or.inl h0
      · right
        intro hp
        have he := h.eq_of_le hp ⟨Nat.sub_le _ _,le_rfl⟩
        have hL := congrArg Prod.fst he
        omega
    · by_cases h0 : c.2=0
      · exact Or.inl h0
      · right
        intro hp
        have he := h.eq_of_le hp ⟨le_rfl,Nat.sub_le _ _⟩
        have hK := congrArg Prod.snd he
        omega
  · rintro ⟨hL,hK⟩
    refine ⟨hc,?_⟩
    intro b hb hbc
    have hbL := hbc.1
    have hbK := hbc.2
    have heL : c.1≤b.1 := by
      by_contra h
      have hp := D.coreFiber_upward r hb (show b≤(c.1-1,c.2) from ⟨by omega,hbK⟩)
      rcases hL with hL|hL <;> first | omega | exact hL hp
    have heK : c.2≤b.2 := by
      by_contra h
      have hp := D.coreFiber_upward r hb (show b≤(c.1,c.2-1) from ⟨hbL,by omega⟩)
      rcases hK with hK|hK <;> first | omega | exact hK hp
    exact ⟨heL,heK⟩

def CoreMinimal (p : D.corePoints) : Prop :=
  Minimal (·∈D.coreFiber (D.coreCoordinates p).1) (D.coreCoordinates p).2

theorem core_not_minimal_iff_factor (p : D.corePoints) : ¬D.CoreMinimal p ↔
    (∃ q : D.corePoints,p=q+D.coreGeneratorPoint D.xVariable) ∨
      (∃ q : D.corePoints,p=q+D.coreGeneratorPoint D.vVariable) := by
  constructor
  · intro hn
    let c := (D.coreCoordinates p).2
    let r := (D.coreCoordinates p).1
    have hc : c∈D.coreFiber r := D.coordinate_mem_fiber p
    have hp : ¬((c.1=0 ∨ (c.1-1,c.2)∉D.coreFiber r) ∧ (c.2=0 ∨ (c.1,c.2-1)∉D.coreFiber r)) := by
      intro h
      exact hn ((D.minimalFiber_iff_predecessors r c hc).mpr h)
    have hor : (0<c.1 ∧ (c.1-1,c.2)∈D.coreFiber r) ∨ (0<c.2 ∧ (c.1,c.2-1)∈D.coreFiber r) := by
      push Not at hp
      by_cases hL : c.1=0 ∨ (c.1-1,c.2)∉D.coreFiber r
      · right
        have hbad := hp hL
        exact ⟨by omega,hbad.2⟩
      · left
        push Not at hL
        exact ⟨by omega,hL.2⟩
    rcases hor with h|h
    · left
      let q : D.corePoints := ⟨D.decodeCoordinate (r,(c.1-1,c.2)),h.2⟩
      refine ⟨q,?_⟩
      apply Subtype.ext
      rw [←D.decode_coreCoordinates p]
      apply Prod.ext
      · change c.1+c.2+D.epsilon r=c.1-1+c.2+D.epsilon r+1
        omega
      · change r.val+D.u*c.2=r.val+D.u*c.2+0
        omega
    · right
      let q : D.corePoints := ⟨D.decodeCoordinate (r,(c.1,c.2-1)),h.2⟩
      refine ⟨q,?_⟩
      apply Subtype.ext
      rw [←D.decode_coreCoordinates p]
      apply Prod.ext
      · change c.1+c.2+D.epsilon r=c.1+(c.2-1)+D.epsilon r+1
        omega
      · change r.val+D.u*c.2=r.val+D.u*(c.2-1)+D.u
        nlinarith [Nat.sub_add_cancel (show 1≤c.2 by omega)]
  · intro h hmin
    rcases h with ⟨q,hq⟩|⟨q,hq⟩
    · have hfac : p=q+D.coreEndpointPoint (1,0) := by simpa [coreEndpointPoint] using hq
      have hh := D.minimal_endpoint_factor p q (1,0) hmin hfac
      have he := congrArg Prod.fst hh
      norm_num at he
    · have hfac : p=q+D.coreEndpointPoint (0,1) := by simpa [coreEndpointPoint] using hq
      have hh := D.minimal_endpoint_factor p q (0,1) hmin hfac
      have he := congrArg Prod.snd hh
      norm_num at he
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CoreArtinIdeal; source SHA256 22f582b292db3434a60d7de5786b97d9703512a99fc5e7b96c26024b6467142a.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

theorem coreEndpointIdeal_generators :
    {a : D.Core k | a∈[D.endpointToCore k (MvPolynomial.X 1),D.endpointToCore k (MvPolynomial.X 0)]}=
      AddMonoidAlgebra.of' k D.corePoints '' {D.coreGeneratorPoint D.xVariable,D.coreGeneratorPoint D.vVariable} := by
  rw [Set.image_insert_eq,Set.image_singleton]
  ext a
  simp only [Set.mem_ofPred_eq,List.mem_cons,List.not_mem_nil,or_false,Set.mem_insert_iff,Set.mem_singleton_iff,
    D.endpointToCore_X]
  change (a=D.coreMonomial k (D.coreGeneratorPoint D.vVariable) ∨ a=D.coreMonomial k (D.coreGeneratorPoint D.xVariable)) ↔
    (a=D.coreMonomial k (D.coreGeneratorPoint D.xVariable) ∨ a=D.coreMonomial k (D.coreGeneratorPoint D.vVariable))
  exact or_comm

/-- The actual endpoint ideal kills exactly nonminimal core monomials,
so arbitrary linear combinations have the expected quotient kernel. -/
theorem coreEndpointIdeal_mem (f : D.Core k) :
    f∈NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k) ↔
      ∀ p∈f.coeff.support,¬D.CoreMinimal p := by
  rw [NSP14.Endpoint.endpointIdeal,D.coreEndpointIdeal_generators,AddMonoidAlgebra.mem_ideal_span_of'_image]
  constructor
  · intro h p hp
    obtain ⟨b,hb,q,hq⟩ := h p hp
    apply (D.core_not_minimal_iff_factor p).mpr
    rcases (show b=D.coreGeneratorPoint D.xVariable ∨ b=D.coreGeneratorPoint D.vVariable by simpa using hb) with rfl|rfl
    · exact Or.inl ⟨q,hq⟩
    · exact Or.inr ⟨q,hq⟩
  · intro h p hp
    rcases (D.core_not_minimal_iff_factor p).mp (h p hp) with ⟨q,hq⟩|⟨q,hq⟩
    · exact ⟨D.coreGeneratorPoint D.xVariable,by simp,q,hq⟩
    · exact ⟨D.coreGeneratorPoint D.vVariable,by simp,q,hq⟩

theorem coreEndpointIdeal_coeff_zero (f : D.Core k) :
    f∈NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k) ↔
      ∀ p,D.CoreMinimal p → f.coeff p=0 := by
  rw [D.coreEndpointIdeal_mem]
  constructor
  · intro h p hp
    by_contra hne
    exact h p (Finsupp.mem_support_iff.mpr hne) hp
  · intro h p hp hmin
    exact (Finsupp.mem_support_iff.mp hp) (h p hmin)
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CoreArtinBasis; source SHA256 a6fbea72468e2217453ea93e510ee70a5c3eeeb82ec245c806b83fa016940d48.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

abbrev CoreMinimalIndex := {p : D.corePoints // D.CoreMinimal p}

noncomputable def coreMinimalIndexEquiv : D.CoreMinimalIndex ≃
    (Σ r : Fin D.u,{c : ℕ×ℕ // Minimal (·∈D.coreFiber r) c}) where
  toFun p := ⟨(D.coreCoordinates p.val).1,⟨(D.coreCoordinates p.val).2,p.property⟩⟩
  invFun c := ⟨⟨D.decodeCoordinate (c.1,c.2.val),c.2.property.prop⟩,by
    change Minimal (·∈D.coreFiber (D.coreCoordinates _).1) (D.coreCoordinates _).2
    rw [D.coreCoordinates_decode]
    exact c.2.property⟩
  left_inv p := by
    apply Subtype.ext
    exact Subtype.ext (D.decode_coreCoordinates p.val)
  right_inv c := by
    rcases c with ⟨r,c,hc⟩
    change (⟨(D.coreCoordinates ⟨D.decodeCoordinate (r,c),hc.prop⟩).1,
      ⟨(D.coreCoordinates ⟨D.decodeCoordinate (r,c),hc.prop⟩).2,_⟩⟩ : Σ r,{c // Minimal (·∈D.coreFiber r) c})=⟨r,⟨c,hc⟩⟩
    have he := D.coreCoordinates_decode r c hc.prop
    exact Sigma.subtype_ext (congrArg Prod.fst he) (congrArg Prod.snd he)

noncomputable instance coreMinimalIndexFinite : Finite D.CoreMinimalIndex := by
  have (r : Fin D.u) : Finite {c | Minimal (·∈D.coreFiber r) c} := (D.minimalFiber_finite r).to_subtype
  exact Finite.of_equiv _ D.coreMinimalIndexEquiv.symm

noncomputable instance coreMinimalIndexFintype : Fintype D.CoreMinimalIndex := Fintype.ofFinite _

variable (k : Type) [Field k]
noncomputable def coreMinimalNormal : (D.CoreMinimalIndex →₀ k) →ₗ[k] D.Core k :=
  (AddMonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.comp
    ((Finsupp.supported k k {p : D.corePoints | D.CoreMinimal p}).subtype.comp
      (Finsupp.supportedEquivFinsupp (R:=k) {p : D.corePoints | D.CoreMinimal p}).symm.toLinearMap)

theorem coreMinimalNormal_coeff (g : D.CoreMinimalIndex →₀ k) :
    (D.coreMinimalNormal k g).coeff=g.extendDomain := rfl

noncomputable def QCoreNormalMap : (D.CoreMinimalIndex →₀ k) →ₗ[k] D.QCore k :=
  (Ideal.Quotient.mkₐ k _).toLinearMap.comp (D.coreMinimalNormal k)

theorem QCoreNormalMap_injective : Function.Injective (D.QCoreNormalMap k) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro g hg
  change Ideal.Quotient.mk _ (D.coreMinimalNormal k g)=0 at hg
  have hm := (D.coreEndpointIdeal_coeff_zero k _).mp (Ideal.Quotient.eq_zero_iff_mem.mp hg)
  apply Finsupp.ext
  intro p
  have hh := hm p.val p.property
  rw [D.coreMinimalNormal_coeff] at hh
  simpa only [Finsupp.extendDomain_apply,dite_eq_left p.property,Finsupp.zero_apply] using hh

theorem QCoreNormalMap_surjective : Function.Surjective (D.QCoreNormalMap k) := by
  intro a
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ a
  let g : D.CoreMinimalIndex →₀ k := f.coeff.subtypeDomain D.CoreMinimal
  refine ⟨g,?_⟩
  change Ideal.Quotient.mk _ (D.coreMinimalNormal k g)=Ideal.Quotient.mk _ f
  apply Ideal.Quotient.eq.mpr
  apply (D.coreEndpointIdeal_coeff_zero k _).mpr
  intro p hp
  simp only [AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,D.coreMinimalNormal_coeff,
    Finsupp.extendDomain_apply,dite_eq_left hp,g,Finsupp.subtypeDomain_apply,sub_self]

/-- Coordinates in the genuine ring quotient QC, indexed by actual
minimal fiber points. No initial ideal or monomial assumption on T is used. -/
noncomputable def QCoreCoordinates : D.QCore k ≃ₗ[k] (D.CoreMinimalIndex →₀ k) :=
  (LinearEquiv.ofBijective (D.QCoreNormalMap k) ⟨D.QCoreNormalMap_injective k,D.QCoreNormalMap_surjective k⟩).symm

noncomputable def QCoreBasis : Module.Basis D.CoreMinimalIndex k (D.QCore k) :=
  Finsupp.basisSingleOne.map (D.QCoreCoordinates k).symm

theorem QCoreBasis_apply (p : D.CoreMinimalIndex) : D.QCoreBasis k p=
    Ideal.Quotient.mk _ (D.coreMonomial k p.val) := by
  change Ideal.Quotient.mk _ (D.coreMinimalNormal k (Finsupp.single p (1:k)))=_
  apply congrArg (Ideal.Quotient.mk _)
  apply (AddMonoidAlgebra.coeffLinearEquiv k).injective
  change (D.coreMinimalNormal k (Finsupp.single p (1:k))).coeff=(D.coreMonomial k p.val).coeff
  rw [D.coreMinimalNormal_coeff,Finsupp.extendDomain_single]
  rfl

theorem coreP_minimalCount : D.coreP k=∑ r : Fin D.u,(D.minimalPoints r).card := by
  rw [coreP,Module.finrank_eq_card_basis (D.QCoreBasis k)]
  have (r : Fin D.u) : Finite {c | Minimal (·∈D.coreFiber r) c} := (D.minimalFiber_finite r).to_subtype
  rw [Fintype.card_eq_nat_card,Nat.card_congr D.coreMinimalIndexEquiv,Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  exact (D.minimalPoints_card_eq r).symm

theorem coreP_le_wordVolume : D.coreP k≤D.wordVolume := by
  rw [D.coreP_minimalCount]
  exact D.minimalCount_volume
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CoreInternalAction; source SHA256 410fdb5d77a3b3f830f7a50d68326afa68f56bb12a45f5d0f2c0c41afd6cef1e.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

theorem internalToCore_X (b : D.a) : D.internalToCore k (MvPolynomial.X b)=
    D.coreMonomial k (D.coreGeneratorPoint (D.internalVariable b)) := by
  simp only [internalToCore,AlgHom.comp_apply,internalToFull,MvPolynomial.rename_X,
    fullToCore,MvPolynomial.aeval_X]

theorem QCore_class_monomial (p : D.corePoints) :
    Ideal.Quotient.mk (NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k)) (D.coreMonomial k p)=
      if h : D.CoreMinimal p then D.QCoreBasis k ⟨p,h⟩ else 0 := by
  split_ifs with h
  · exact (D.QCoreBasis_apply k ⟨p,h⟩).symm
  · apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [D.coreEndpointIdeal_mem]
    intro q hq
    have he : p=q := by
      by_contra hn
      have hz : (D.coreMonomial k p).coeff q=0 := by
        change (Finsupp.single p (1:k)) q=0
        exact Finsupp.single_eq_of_ne (Ne.symm hn)
      exact (Finsupp.mem_support_iff.mp hq) hz
    simpa only [←he] using h

/-- Actual internal multiplication on QC. A nonminimal destination is
zero; a minimal destination is precisely its genuine basis class. -/
theorem QCore_internal_basis (b : D.a) (p : D.CoreMinimalIndex) :
    D.internalToQCore k (MvPolynomial.X b)*D.QCoreBasis k p=
      if h : D.CoreMinimal (p.val+D.coreGeneratorPoint (D.internalVariable b)) then
        D.QCoreBasis k ⟨p.val+D.coreGeneratorPoint (D.internalVariable b),h⟩ else 0 := by
  rw [D.QCoreBasis_apply]
  change Ideal.Quotient.mk _ (D.internalToCore k (MvPolynomial.X b))*
    Ideal.Quotient.mk _ (D.coreMonomial k p.val)=_
  rw [←map_mul,D.internalToCore_X,D.coreMonomial_mul,add_comm,D.QCore_class_monomial]

theorem coreMinimal_degree_lt (p : D.CoreMinimalIndex) : D.coreDegree p.val<D.u := by
  have h := D.minimalFiber_degree_lt (D.coreCoordinates p.val).1 (D.coreCoordinates p.val).2 p.property
  have hd := congrArg Prod.fst (D.decode_coreCoordinates p.val)
  change (D.coreCoordinates p.val).2.1+(D.coreCoordinates p.val).2.2+D.epsilon (D.coreCoordinates p.val).1=D.coreDegree p.val at hd
  omega
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CoreInternalPresentation; source SHA256 60d1a97c6331ee2ceb46a4706c932161fd71e8c4974196a29a9da3172c8d8427.
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

noncomputable def wordPolynomial (w : List D.Variables) : D.FullRing k := (w.map MvPolynomial.X).prod

theorem fullToCore_wordPolynomial (w : List D.Variables) :
    D.fullToCore k (D.wordPolynomial k w)=D.coreMonomial k (D.coreWord w) := by
  induction w with
  | nil =>
    change D.fullToCore k 1=D.coreMonomial k 0
    rw [map_one]
    rfl
  | cons b w ih =>
    change D.fullToCore k (MvPolynomial.X b*D.wordPolynomial k w)=_
    rw [map_mul,show D.fullToCore k (MvPolynomial.X b)=D.coreMonomial k (D.coreGeneratorPoint b) by simp [fullToCore],ih,
      D.coreMonomial_mul,D.coreWord_cons]

theorem fullToCore_surjective : Function.Surjective (D.fullToCore k) := by
  intro f
  induction f using AddMonoidAlgebra.induction_on with
  | of p =>
    obtain ⟨w,hw⟩ := D.exists_coreWord p
    refine ⟨D.wordPolynomial k w,?_⟩
    rw [D.fullToCore_wordPolynomial,hw]
    rfl
  | add a b ha hb =>
    obtain ⟨p,hp⟩ := ha
    obtain ⟨q,hq⟩ := hb
    exact ⟨p+q,by rw [map_add,hp,hq]⟩
  | smul c a ha =>
    obtain ⟨p,hp⟩ := ha
    exact ⟨c • p,by rw [map_smul,hp]⟩

noncomputable def removeEndpoints : D.FullRing k →ₐ[k] D.InternalRing k :=
  MvPolynomial.aeval (fun b : D.Variables => if h : b.val∈D.a then MvPolynomial.X ⟨b.val,h⟩ else 0)

theorem QCore_endpoint_zero (i : Fin 2) :
    Ideal.Quotient.mk (NSP14.Endpoint.endpointIdeal k (D.Core k) (D.endpointToCore k))
      (D.endpointToCore k (MvPolynomial.X i))=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.subset_span
  fin_cases i <;> simp

theorem removeEndpoints_QCore : (D.internalToQCore k).comp (D.removeEndpoints k)=
    (Ideal.Quotient.mkₐ k _).comp (D.fullToCore k) := by
  apply MvPolynomial.algHom_ext
  intro b
  change D.internalToQCore k (D.removeEndpoints k (MvPolynomial.X b))=
    Ideal.Quotient.mk _ (D.fullToCore k (MvPolynomial.X b))
  simp only [removeEndpoints,MvPolynomial.aeval_X]
  split_ifs with hb
  · change Ideal.Quotient.mk _ (D.fullToCore k (D.internalToFull k (MvPolynomial.X ⟨b.val,hb⟩)))=_
    rw [internalToFull,MvPolynomial.rename_X]
    rfl
  · rcases (D.mem_offsets b.val).mp b.property with h0|hu|ha
    · have he : b=D.xVariable := Subtype.ext h0
      subst b
      rw [map_zero]
      simpa [endpointToCore,endpointToFull,endpointVariable] using (D.QCore_endpoint_zero k 0).symm
    · have he : b=D.vVariable := Subtype.ext hu
      subst b
      rw [map_zero]
      simpa [endpointToCore,endpointToFull,endpointVariable] using (D.QCore_endpoint_zero k 1).symm
    · exact (hb ha).elim

/-- QC is generated by its actual q internal degree-one images. The
endpoint images are killed in the genuine quotient, not set to zero in G. -/
theorem internalToQCore_surjective : Function.Surjective (D.internalToQCore k) := by
  intro a
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mkₐ_surjective k _ a
  obtain ⟨p,hp⟩ := D.fullToCore_surjective k f
  refine ⟨D.removeEndpoints k p,?_⟩
  have he := AlgHom.congr_fun (D.removeEndpoints_QCore k) p
  change D.internalToQCore k (D.removeEndpoints k p)=Ideal.Quotient.mk _ (D.fullToCore k p) at he
  rw [hp] at he
  exact he
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Endpoint.CoreAugmentation; source SHA256 00ef7d60213354ba2106d12452f2c82e646926264ef3232caac166891b1c04cb.
set_option backward.isDefEq.respectTransparency false
open CategoryTheory NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData) (k : Type) [Field k]

theorem fullToG_augmentation_X (b : D.Variables) :
    D.source.tangentAugmentation k (D.fullToG k (MvPolynomial.X b))=0 := by
  have h := AlgHom.congr_fun (D.source.tangentAugmentation_polynomial k) (MvPolynomial.X (D.atomVariable b))
  change D.source.tangentAugmentation k (D.source.fullPolynomialToG k (MvPolynomial.X (D.atomVariable b)))=_ at h
  rw [D.source.fullPolynomialToG_X,augmentation_X] at h
  rw [D.fullToG_X]
  exact h

theorem actual_endpointIdeal_augmentation :
    NSP14.Endpoint.endpointIdeal k (D.source.TangentAlgebra k) (D.endpointToG k)≤
      RingHom.ker (D.source.tangentAugmentation k).toRingHom := by
  apply Ideal.span_le.mpr
  intro a ha
  have he (i : Fin 2) : D.source.tangentAugmentation k (D.endpointToG k (MvPolynomial.X i))=0 := by
    simp only [endpointToG,AlgHom.comp_apply,endpointToFull,MvPolynomial.rename_X]
    exact D.fullToG_augmentation_X k _
  rcases (show a=D.endpointToG k (MvPolynomial.X 1) ∨ a=D.endpointToG k (MvPolynomial.X 0) by simpa using ha) with rfl|rfl
  · exact he 1
  · exact he 0

noncomputable def QActualAugmentation : D.QActual k →ₐ[k] k :=
  Ideal.Quotient.liftₐ _ (D.source.tangentAugmentation k) (D.actual_endpointIdeal_augmentation k)

noncomputable def QCoreAugmentation : D.QCore k →ₐ[k] k := (D.QActualAugmentation k).comp (D.QCoreToActual k)

theorem QCore_augmentation_polynomial : (D.QCoreAugmentation k).comp (D.internalToQCore k)=augmentation k D.a := by
  apply MvPolynomial.algHom_ext
  intro b
  change D.QActualAugmentation k (D.QCoreToActual k (D.internalToQCore k (MvPolynomial.X b)))=_
  rw [D.QCoreToActual_internal]
  change D.source.tangentAugmentation k (D.internalToG k (MvPolynomial.X b))=augmentation k D.a (MvPolynomial.X b)
  rw [augmentation_X]
  simp only [internalToG,AlgHom.comp_apply,internalToFull,MvPolynomial.rename_X]
  exact D.fullToG_augmentation_X k _

theorem QCore_betti_zero : totalBetti k D.a (D.QCoreModule k) 0=1 :=
  regularAugmented_totalBetti_zero k D.a (D.QCore k) (D.internalToQCore k) (D.QCoreAugmentation k)
    (D.internalToQCore_surjective k) (D.QCore_augmentation_polynomial k)
end NSP14.SmallEmbedding.ThreeData

-- Replayed common endpoint module: NSP14.Width.EdgeAP; source SHA256 72f33fd2cc4b0644cf92613cbc01eb99689f98956619087c82a95b514be5b277.
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
open scoped Classical
open NSP14.Homological
namespace NSP14.SmallEmbedding.ThreeData
variable (D : NSP14.SmallEmbedding.ThreeData)

theorem fullAP_offsets (hu : D.u=D.q+1) : D.offsets=Finset.range (D.u+1) := by
  apply Finset.eq_of_subset_of_card_le
  · intro b hb
    exact Finset.mem_range.mpr (by have := D.offset_le hb; omega)
  · rw [Finset.card_range,D.offsets_card]
    omega

/-- The actual full offset interval is an arithmetic-sequence source,
with the original m and original unrestricted common difference. -/
def fullAP : NSP14.ArithmeticSequence.Data where
  m := D.m
  d := D.d
  v := D.u
  m_two := by have := D.u_pos; have := D.u_lt; omega
  d_pos := D.d_pos
  v_pos := D.u_pos
  v_lt := D.u_lt
  coprime := D.coprime

theorem fullAP_carrier (hu : D.u=D.q+1) : D.source.carrier=D.fullAP.source.carrier := by
  apply le_antisymm
  · apply AddSubmonoid.closure_le.mpr
    intro n hn
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hn
    exact D.fullAP.generator_mem b (D.offset_le hb)
  · rw [←D.fullAP.source.closure_atoms]
    apply AddSubmonoid.closure_le.mpr
    intro n hn
    obtain ⟨b,hb,rfl⟩ := D.fullAP.atom_eq_generator ((D.fullAP.source.mem_atoms_iff n).mp hn)
    apply D.source_generator
    rw [D.fullAP_offsets hu]
    exact Finset.mem_range.mpr (by change b ≤ D.u at hb; omega)
end NSP14.SmallEmbedding.ThreeData
