module
public import NSP14.NarrowFour.WidthFourCompetitors
public import NSP14.Width.IdealGeneratorBound
public import NSP14.Endpoint.Nilpotence
public import NSP14.Homological.GradedCyclicPresentation
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NarrowFour.WidthFour
section Reduction
variable {A : Type} [CommRing A] (x y z v : A)

def evalWord (L s t K : ℕ) : A := x^L*y^s*z^t*v^K

theorem reduce_y3 (L s t K : ℕ) (hs : 3 ≤ s) (hy : y^3=x^2*z) :
    evalWord x y z v L s t K=evalWord x y z v (L+2) (s-3) (t+1) K := by
  have he : s=s-3+3 := by omega
  calc
    _=x^L*y^(s-3)*y^3*z^t*v^K := by
      conv_lhs => rw [evalWord,he,pow_add]
      ring
    _=_ := by rw [hy];simp only [evalWord,pow_add,pow_one];ring

theorem reduce_yz (L s t K : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hyz : y*z=x*v) :
    evalWord x y z v L s t K=evalWord x y z v (L+1) (s-1) (t-1) (K+1) := by
  have he : s=s-1+1 := by omega
  have hf : t=t-1+1 := by omega
  calc
    _=(x^L*y^(s-1)*z^(t-1)*v^K)*(y*z) := by
      conv_lhs => rw [evalWord,he,hf,pow_add,pow_add]
      simp only [pow_one]
      ring
    _=_ := by rw [hyz];simp only [evalWord,pow_add,pow_one];ring

theorem reduce_z3 (L s t K : ℕ) (ht : 3 ≤ t) (hz : z^3=y*v^2) :
    evalWord x y z v L s t K=evalWord x y z v L (s+1) (t-3) (K+2) := by
  have he : t=t-3+3 := by omega
  calc
    _=(x^L*y^s*z^(t-3)*v^K)*z^3 := by
      conv_lhs => rw [evalWord,he,pow_add]
      ring
    _=_ := by rw [hz];simp only [evalWord,pow_add,pow_one];ring

theorem reduce_xz2 (L s t K : ℕ) (hL : 1 ≤ L) (ht : 2 ≤ t) (hxz : x*z^2=y^2*v) :
    evalWord x y z v L s t K=evalWord x y z v (L-1) (s+2) (t-2) (K+1) := by
  have he : L=L-1+1 := by omega
  have hf : t=t-2+2 := by omega
  calc
    _=(x^(L-1)*y^s*z^(t-2)*v^K)*(x*z^2) := by
      conv_lhs => rw [evalWord,he,hf,pow_add,pow_add]
      simp only [pow_one]
      ring
    _=_ := by rw [hxz];simp only [evalWord,pow_add,pow_one];ring

def evalColumn (p : Column) : A := evalWord x y z v p.L (anchorY p.anchor) (anchorZ p.anchor) p.K

end Reduction

theorem reduced_column (L s t K : ℕ) (hs : s<3) (ht : t<3)
    (hst : ¬(1 ≤ s ∧ 1 ≤ t)) (hL : 2 ≤ t → L=0) :
    ∃ p : Column,p.L=L ∧ p.K=K ∧ anchorY p.anchor=s ∧ anchorZ p.anchor=t := by
  have hc : (s=0 ∧ t=0) ∨ (s=1 ∧ t=0) ∨ (s=2 ∧ t=0) ∨ (s=0 ∧ t=1) ∨ (s=0 ∧ t=2) := by omega
  rcases hc with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact ⟨⟨0,L,K,by simp⟩,rfl,rfl,rfl,rfl⟩
  · exact ⟨⟨1,L,K,by simp⟩,rfl,rfl,rfl,rfl⟩
  · exact ⟨⟨2,L,K,by simp⟩,rfl,rfl,rfl,rfl⟩
  · exact ⟨⟨3,L,K,by simp⟩,rfl,rfl,rfl,rfl⟩
  · exact ⟨⟨4,L,K,by intro _;exact hL (by omega)⟩,rfl,rfl,rfl,rfl⟩

section NormalSpan
variable (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A]
    (x y z v : A) (m : ℕ)

def liveSpan : Submodule k A := Submodule.span k
  (evalColumn x y z v '' {p : Column | p.K<theta m (anchorN p.anchor)})

theorem evalColumn_mem
    (htail : ∀ i : Fin 5,y^(anchorY i)*z^(anchorZ i)*v^(theta m (anchorN i))=0)
    (p : Column) : evalColumn x y z v p∈liveSpan k A x y z v m := by
  by_cases hK : p.K<theta m (anchorN p.anchor)
  · exact Submodule.subset_span ⟨p,hK,rfl⟩
  · have he : p.K=theta m (anchorN p.anchor)+(p.K-theta m (anchorN p.anchor)) := by omega
    have hz : evalColumn x y z v p=0 := by
      calc
        _=x^p.L*(y^(anchorY p.anchor)*z^(anchorZ p.anchor)*v^(theta m (anchorN p.anchor)))*
            v^(p.K-theta m (anchorN p.anchor)) := by
          conv_lhs => rw [evalColumn,evalWord,he,pow_add]
          ring
        _=0 := by rw [htail];simp
    rw [hz]
    exact (liveSpan k A x y z v m).zero_mem

/-- Termination uses the strictly decreasing original internal weight s+2t.
No unproved Gröbner/Betti comparison is used. -/
theorem evalWord_mem
    (hy : y^3=x^2*z) (hyz : y*z=x*v) (hxz : x*z^2=y^2*v) (hz : z^3=y*v^2)
    (htail : ∀ i : Fin 5,y^(anchorY i)*z^(anchorZ i)*v^(theta m (anchorN i))=0)
    (L s t K : ℕ) : evalWord x y z v L s t K∈liveSpan k A x y z v m := by
  suffices hall : ∀ n L s t K : ℕ,s+2*t=n →
      evalWord x y z v L s t K∈liveSpan k A x y z v m from hall (s+2*t) L s t K rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro L s t K hn
    by_cases hs : 3 ≤ s
    · rw [reduce_y3 x y z v L s t K hs hy]
      exact ih (s-3+2*(t+1)) (by omega) (L+2) (s-3) (t+1) K rfl
    by_cases hst : 1 ≤ s ∧ 1 ≤ t
    · rw [reduce_yz x y z v L s t K hst.1 hst.2 hyz]
      exact ih (s-1+2*(t-1)) (by omega) (L+1) (s-1) (t-1) (K+1) rfl
    by_cases ht : 3 ≤ t
    · rw [reduce_z3 x y z v L s t K ht hz]
      exact ih (s+1+2*(t-3)) (by omega) L (s+1) (t-3) (K+2) rfl
    by_cases hLt : 1 ≤ L ∧ 2 ≤ t
    · rw [reduce_xz2 x y z v L s t K hLt.1 hLt.2 hxz]
      exact ih (s+2+2*(t-2)) (by omega) (L-1) (s+2) (t-2) (K+1) rfl
    obtain ⟨p,hpL,hpK,hpY,hpZ⟩ := reduced_column L s t K (by omega) (by omega) hst (by omega)
    have hp := evalColumn_mem k A x y z v m htail p
    simpa only [evalColumn,hpL,hpK,hpY,hpZ] using hp
end NormalSpan


abbrev P (k : Type) [CommRing k] := MvPolynomial (Fin 4) k

noncomputable def wordPolynomial (k : Type) [CommRing k] (L s t K : ℕ) : P k :=
  evalWord (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3) L s t K

noncomputable def columnPolynomial (k : Type) [CommRing k] (p : Column) : P k :=
  wordPolynomial k p.L (anchorY p.anchor) (anchorZ p.anchor) p.K

noncomputable def coreRelation (k : Type) [CommRing k] (i : Fin 4) : P k := match i.val with
  | 0 => MvPolynomial.X 1^3-MvPolynomial.X 0^2*MvPolynomial.X 2
  | 1 => MvPolynomial.X 1*MvPolynomial.X 2-MvPolynomial.X 0*MvPolynomial.X 3
  | 2 => MvPolynomial.X 0*MvPolynomial.X 2^2-MvPolynomial.X 1^2*MvPolynomial.X 3
  | _ => MvPolynomial.X 2^3-MvPolynomial.X 1*MvPolynomial.X 3^2

noncomputable def tailRelation (k : Type) [CommRing k] (m : ℕ) (i : Fin 5) : P k :=
  MvPolynomial.X 1^(anchorY i)*MvPolynomial.X 2^(anchorZ i)*MvPolynomial.X 3^(theta m (anchorN i))

noncomputable def relation (k : Type) [CommRing k] (m : ℕ) : Fin 4 ⊕ Fin 5 → P k :=
  Sum.elim (coreRelation k) (tailRelation k m)

noncomputable def candidateIdeal (k : Type) [CommRing k] (m : ℕ) : Ideal (P k) := Ideal.span (Set.range (relation k m))
abbrev Candidate (k : Type) [CommRing k] (m : ℕ) := P k ⧸ candidateIdeal k m

noncomputable def candidateMap (k : Type) [Field k] (m : ℕ) : P k →ₐ[k] Candidate k m :=
  Ideal.Quotient.mkₐ k (candidateIdeal k m)

noncomputable def candidateVariable (k : Type) [Field k] (m : ℕ) (i : Fin 4) : Candidate k m :=
  candidateMap k m (MvPolynomial.X i)

section PolynomialSpan
variable (k : Type) [Field k]

theorem monomial_factor (a : Fin 4 →₀ ℕ) (c : k) :
    MvPolynomial.monomial a c=MvPolynomial.C c*wordPolynomial k (a 0) (a 1) (a 2) (a 3) := by
  rw [MvPolynomial.monomial_eq,Finsupp.prod_fintype _ _ (by intro i;exact pow_zero _),Fin.prod_univ_four]
  rfl

theorem map_wordPolynomial (A : Type) [CommRing A] [Algebra k A] (φ : P k →ₐ[k] A) (L s t K : ℕ) :
    φ (wordPolynomial k L s t K)=evalWord (φ (MvPolynomial.X 0)) (φ (MvPolynomial.X 1))
      (φ (MvPolynomial.X 2)) (φ (MvPolynomial.X 3)) L s t K := by
  simp only [wordPolynomial,evalWord,map_mul,map_pow]

theorem candidate_relation_zero (m : ℕ) (i : Fin 4 ⊕ Fin 5) :
    candidateMap k m (relation k m i)=0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)

theorem candidate_core_relations (m : ℕ) :
    let x := candidateVariable k m 0
    let y := candidateVariable k m 1
    let z := candidateVariable k m 2
    let v := candidateVariable k m 3
    y^3=x^2*z ∧ y*z=x*v ∧ x*z^2=y^2*v ∧ z^3=y*v^2 := by
  have h0 := candidate_relation_zero k m (Sum.inl 0)
  have h1 := candidate_relation_zero k m (Sum.inl 1)
  have h2 := candidate_relation_zero k m (Sum.inl 2)
  have h3 := candidate_relation_zero k m (Sum.inl 3)
  change candidateMap k m ((MvPolynomial.X 1)^3-(MvPolynomial.X 0)^2*MvPolynomial.X 2)=0 at h0
  change candidateMap k m (MvPolynomial.X 1*MvPolynomial.X 2-MvPolynomial.X 0*MvPolynomial.X 3)=0 at h1
  change candidateMap k m (MvPolynomial.X 0*(MvPolynomial.X 2)^2-(MvPolynomial.X 1)^2*MvPolynomial.X 3)=0 at h2
  change candidateMap k m ((MvPolynomial.X 2)^3-MvPolynomial.X 1*(MvPolynomial.X 3)^2)=0 at h3
  simp only [map_sub,map_pow,map_mul,sub_eq_zero] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

theorem candidate_tail_relations (m : ℕ) (i : Fin 5) :
    (candidateVariable k m 1)^(anchorY i)*(candidateVariable k m 2)^(anchorZ i)*
      (candidateVariable k m 3)^(theta m (anchorN i))=0 := by
  have h := candidate_relation_zero k m (Sum.inr i)
  simpa only [candidateVariable,relation,Sum.elim_inr,tailRelation,map_mul,map_pow] using h

/-- The candidate quotient is spanned by exactly the nonforbidden five columns. -/
theorem candidate_spanned (m : ℕ) (q : Candidate k m) :
    q∈liveSpan k (Candidate k m) (candidateVariable k m 0) (candidateVariable k m 1)
      (candidateVariable k m 2) (candidateVariable k m 3) m := by
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mkₐ_surjective k (candidateIdeal k m) q
  change candidateMap k m f∈_
  obtain ⟨hy,hyz,hxz,hz⟩ := candidate_core_relations k m
  induction f using MvPolynomial.induction_on' with
  | add f g hf hg => exact (liveSpan _ _ _ _ _ _ _).add_mem hf hg
  | monomial a c =>
    rw [monomial_factor,map_mul]
    have hφ : candidateMap k m (MvPolynomial.C c)=algebraMap k (Candidate k m) c := (candidateMap k m).commutes c
    rw [hφ,map_wordPolynomial]
    have hp := evalWord_mem k (Candidate k m) _ _ _ _ m hy hyz hxz hz
      (candidate_tail_relations k m) (a 0) (a 1) (a 2) (a 3)
    simpa only [Algebra.smul_def,candidateVariable] using (liveSpan _ _ _ _ _ _ _).smul_mem c hp
end PolynomialSpan


section ActualPresentation
variable (D : Endpoint.Data)

def label (i : Fin 4) : ℕ := match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | _ => 4

def routedVariable (hu : D.u=4) (ha : D.a={1,3}) (i : Fin 4) : D.Variables :=
  ⟨label i,by fin_cases i <;> simp [label,Endpoint.Data.offsets,hu,ha]⟩

theorem routedVariable_injective (hu : D.u=4) (ha : D.a={1,3}) : Function.Injective (routedVariable D hu ha) := by
  intro i j h
  have hv := congrArg (fun z : D.Variables => z.val) h
  fin_cases i <;> fin_cases j <;> norm_num [routedVariable,label] at *

theorem routedVariable_surjective (hu : D.u=4) (ha : D.a={1,3}) : Function.Surjective (routedVariable D hu ha) := by
  intro b
  rcases (D.mem_offsets b.val).mp b.property with h0|h4|h13
  · exact ⟨0,Subtype.ext h0.symm⟩
  · refine ⟨3,Subtype.ext ?_⟩
    change 4=b.val
    omega
  · rw [ha] at h13
    rcases Finset.mem_insert.mp h13 with h1|h3
    · exact ⟨1,Subtype.ext h1.symm⟩
    · exact ⟨2,Subtype.ext (Finset.mem_singleton.mp h3).symm⟩

noncomputable def variableEquiv (hu : D.u=4) (ha : D.a={1,3}) : Fin 4 ≃ D.Variables :=
  Equiv.ofBijective (routedVariable D hu ha) ⟨routedVariable_injective D hu ha,routedVariable_surjective D hu ha⟩

variable (k : Type) [Field k]
noncomputable def renameVariables (hu : D.u=4) (ha : D.a={1,3}) : P k ≃ₐ[k] D.FullRing k :=
  MvPolynomial.renameEquiv k (variableEquiv D hu ha)

noncomputable def toCore (hu : D.u=4) (ha : D.a={1,3}) : P k →ₐ[k] D.Core k :=
  (D.fullToCore k).comp (renameVariables D k hu ha).toAlgHom

noncomputable def toActual (hu : D.u=4) (ha : D.a={1,3}) : P k →ₐ[k] D.source.TangentAlgebra k :=
  (D.coreToG k).comp (toCore D k hu ha)

theorem toCore_surjective (hu : D.u=4) (ha : D.a={1,3}) : Function.Surjective (toCore D k hu ha) :=
  (D.fullToCore_surjective k).comp (renameVariables D k hu ha).surjective

theorem toActual_surjective (hu : D.u=4) (ha : D.a={1,3}) : Function.Surjective (toActual D k hu ha) :=
  (D.coreToG_surjective k).comp (toCore_surjective D k hu ha)

theorem toActual_full (hu : D.u=4) (ha : D.a={1,3}) :
    toActual D k hu ha=(D.fullToG k).comp (renameVariables D k hu ha).toAlgHom := by
  apply AlgHom.ext
  intro f
  exact AlgHom.congr_fun (D.coreToG_fullToCore k) ((renameVariables D k hu ha) f)

theorem toCore_X (hu : D.u=4) (ha : D.a={1,3}) (i : Fin 4) :
    toCore D k hu ha (MvPolynomial.X i)=D.coreMonomial k (D.coreGeneratorPoint (routedVariable D hu ha i)) := by
  change D.fullToCore k ((renameVariables D k hu ha) (MvPolynomial.X i))=_
  rw [renameVariables,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  change D.fullToCore k (MvPolynomial.X (routedVariable D hu ha i))=_
  simp only [Endpoint.Data.fullToCore,MvPolynomial.aeval_X]


def wordPoint (ha : D.a={1,3}) (L s t K : ℕ) : D.corePoints :=
  D.coreEndpointPoint (L,K)+word D (y D ha) (z D ha) s t

theorem wordPoint_coe (hu : D.u=4) (ha : D.a={1,3}) (L s t K : ℕ) :
    (wordPoint D ha L s t K).val=(L+s+t+K,s+3*t+4*K) := by
  change (D.coreEndpointPoint (L,K)).val+(word D (y D ha) (z D ha) s t).val=_
  rw [D.coreEndpointPoint_coe,word_coe,hu]
  apply Prod.ext <;> dsimp [y,z] <;> omega

theorem toCore_wordPolynomial (hu : D.u=4) (ha : D.a={1,3}) (L s t K : ℕ) :
    toCore D k hu ha (wordPolynomial k L s t K)=D.coreMonomial k (wordPoint D ha L s t K) := by
  rw [map_wordPolynomial]
  simp only [evalWord,toCore_X,D.coreMonomial_pow,D.coreMonomial_mul]
  apply congrArg (D.coreMonomial k)
  apply Subtype.ext
  rw [wordPoint_coe D hu ha]
  change (L • (1,0)+s • (1,1)+t • (1,3)+K • (1,4) : ℕ×ℕ)=_
  apply Prod.ext
  · simp
  · simp;omega

theorem toCore_words_eq (hu : D.u=4) (ha : D.a={1,3}) (L s t K L' s' t' K' : ℕ)
    (hdeg : L+s+t+K=L'+s'+t'+K') (hoff : s+3*t+4*K=s'+3*t'+4*K') :
    toCore D k hu ha (wordPolynomial k L s t K)=toCore D k hu ha (wordPolynomial k L' s' t' K') := by
  rw [toCore_wordPolynomial,toCore_wordPolynomial]
  apply congrArg (D.coreMonomial k)
  apply Subtype.ext
  rw [wordPoint_coe D hu ha,wordPoint_coe D hu ha]
  exact Prod.ext hdeg hoff




theorem toCore_coreRelation_zero (hu : D.u=4) (ha : D.a={1,3}) (i : Fin 4) :
    toCore D k hu ha (coreRelation k i)=0 := by
  fin_cases i
  · have he : coreRelation k (⟨0,by decide⟩ : Fin 4)=wordPolynomial k 0 3 0 0-wordPolynomial k 2 0 1 0 := by
      simp [coreRelation,wordPolynomial,evalWord]
    rw [he,map_sub]
    apply sub_eq_zero.mpr
    exact toCore_words_eq D k hu ha 0 3 0 0 2 0 1 0 (by decide) (by decide)
  · have he : coreRelation k (⟨1,by decide⟩ : Fin 4)=wordPolynomial k 0 1 1 0-wordPolynomial k 1 0 0 1 := by
      simp [coreRelation,wordPolynomial,evalWord]
    rw [he,map_sub]
    apply sub_eq_zero.mpr
    exact toCore_words_eq D k hu ha 0 1 1 0 1 0 0 1 (by decide) (by decide)
  · have he : coreRelation k (⟨2,by decide⟩ : Fin 4)=wordPolynomial k 1 0 2 0-wordPolynomial k 0 2 0 1 := by
      simp [coreRelation,wordPolynomial,evalWord]
    rw [he,map_sub]
    apply sub_eq_zero.mpr
    exact toCore_words_eq D k hu ha 1 0 2 0 0 2 0 1 (by decide) (by decide)
  · have he : coreRelation k (⟨3,by decide⟩ : Fin 4)=wordPolynomial k 0 0 3 0-wordPolynomial k 0 1 0 2 := by
      simp [coreRelation,wordPolynomial,evalWord]
    rw [he,map_sub]
    apply sub_eq_zero.mpr
    exact toCore_words_eq D k hu ha 0 0 3 0 0 1 0 2 (by decide) (by decide)

theorem toActual_tailRelation_zero (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) (i : Fin 5) :
    toActual D k hu ha (tailRelation k D.m i)=0 := by
  let p : Column := ⟨i,0,theta D.m (anchorN i),by intro _;rfl⟩
  have hpoly : tailRelation k D.m i=columnPolynomial k p := by
    simp [columnPolynomial,wordPolynomial,tailRelation,evalWord,p]
  rw [hpoly]
  change D.coreToG k (toCore D k hu ha (columnPolynomial k p))=0
  rw [columnPolynomial,toCore_wordPolynomial]
  change D.coreToG k (D.coreMonomial k (columnPoint D ha p))=0
  exact (column_zero_iff D k hm hd hu ha p).mpr le_rfl

theorem candidate_le_kernel (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) :
    candidateIdeal k D.m ≤ RingHom.ker (toActual D k hu ha).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f ⟨i,rfl⟩
  change toActual D k hu ha (relation k D.m i)=0
  cases i with
  | inl i =>
    change D.coreToG k (toCore D k hu ha (coreRelation k i))=0
    rw [toCore_coreRelation_zero,map_zero]
  | inr i => exact toActual_tailRelation_zero D k hm hd hu ha i

noncomputable def candidateLift (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) :
    Candidate k D.m →ₐ[k] D.source.TangentAlgebra k :=
  Ideal.Quotient.liftₐ (candidateIdeal k D.m) (toActual D k hu ha) (candidate_le_kernel D k hm hd hu ha)

theorem candidateLift_map (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) (f : P k) :
    candidateLift D k hm hd hu ha (candidateMap k D.m f)=toActual D k hu ha f := rfl




theorem candidateMap_columnPolynomial (m : ℕ) (p : Column) :
    candidateMap k m (columnPolynomial k p)=evalColumn (candidateVariable k m 0)
      (candidateVariable k m 1) (candidateVariable k m 2) (candidateVariable k m 3) p := by
  rw [columnPolynomial,map_wordPolynomial]
  rfl

theorem toCore_columnPolynomial (hu : D.u=4) (ha : D.a={1,3}) (p : Column) :
    toCore D k hu ha (columnPolynomial k p)=D.coreMonomial k (columnPoint D ha p) := by
  rw [columnPolynomial,toCore_wordPolynomial]
  rfl

theorem candidateLift_live (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) (p : LiveColumn D.m) :
    candidateLift D k hm hd hu ha (evalColumn (candidateVariable k D.m 0)
      (candidateVariable k D.m 1) (candidateVariable k D.m 2) (candidateVariable k D.m 3) p.val)=liveImage D k ha p := by
  rw [←candidateMap_columnPolynomial,candidateLift_map]
  change D.coreToG k (toCore D k hu ha (columnPolynomial k p.val))=_
  rw [toCore_columnPolynomial]
  rfl

/-- Surjectivity of normal forms and actual coefficient duals close injectivity;
no equality of Hilbert series or finite-dimensional finrank is substituted for this map. -/
theorem candidateLift_injective (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) :
    Function.Injective (candidateLift D k hm hd hu ha) := by
  let w : Column → Candidate k D.m := evalColumn (candidateVariable k D.m 0)
    (candidateVariable k D.m 1) (candidateVariable k D.m 2) (candidateVariable k D.m 3)
  let v : LiveColumn D.m → Candidate k D.m := fun p => w p.val
  have hrange : Set.range v=w '' {p : Column | p.K<theta D.m (anchorN p.anchor)} := by
    ext a
    constructor
    · rintro ⟨p,rfl⟩
      exact ⟨p.val,p.property,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨⟨p,hp⟩,rfl⟩
  have hspan : Submodule.span k (Set.range v)=⊤ := by
    apply top_unique
    intro a _
    rw [hrange]
    exact candidate_spanned k D.m a
  apply LinearMap.injective_of_linearIndependent (f := (candidateLift D k hm hd hu ha).toLinearMap) hspan
  have he : (candidateLift D k hm hd hu ha).toLinearMap ∘ v=liveImage D k ha := by
    funext p
    exact candidateLift_live D k hm hd hu ha p
  rw [he]
  exact live_images_independent D k hm hd hu ha

/-- Explicit equality of the actual defining kernel with the candidate ideal. -/
theorem actual_kernel_eq (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) :
    RingHom.ker (toActual D k hu ha).toRingHom=candidateIdeal k D.m := by
  apply le_antisymm _ (candidate_le_kernel D k hm hd hu ha)
  intro f hf
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h : candidateLift D k hm hd hu ha (candidateMap k D.m f)=candidateLift D k hm hd hu ha 0 := by
    rw [candidateLift_map,map_zero]
    exact hf
  exact candidateLift_injective D k hm hd hu ha h

noncomputable def actualPresentation (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) :
    Candidate k D.m ≃ₐ[k] D.source.TangentAlgebra k :=
  AlgEquiv.ofBijective (candidateLift D k hm hd hu ha) ⟨candidateLift_injective D k hm hd hu ha,by
    intro a
    obtain ⟨p,hp⟩ := toActual_surjective D k hu ha a
    exact ⟨candidateMap k D.m p,by rw [candidateLift_map,hp]⟩⟩



theorem toActual_augmentation (hu : D.u=4) (ha : D.a={1,3}) :
    (D.source.tangentAugmentation k).comp (toActual D k hu ha)=NSP14.Homological.augmentation k (Fin 4) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply,NSP14.Homological.augmentation_X]
  rw [toActual_full]
  change D.source.tangentAugmentation k (D.fullToG k ((renameVariables D k hu ha) (MvPolynomial.X i)))=0
  rw [renameVariables,MvPolynomial.renameEquiv_apply,MvPolynomial.rename_X]
  exact D.fullToG_augmentation_X k _

theorem candidate_augmentation (hm : 6 ≤ D.m) (hd : D.d=1) (hu : D.u=4) (ha : D.a={1,3}) :
    candidateIdeal k D.m ≤ RingHom.ker (NSP14.Homological.augmentation k (Fin 4)).toRingHom := by
  intro f hf
  have hz : toActual D k hu ha f=0 := candidate_le_kernel D k hm hd hu ha hf
  have he := AlgHom.congr_fun (toActual_augmentation D k hu ha) f
  change D.source.tangentAugmentation k (toActual D k hu ha f)=NSP14.Homological.augmentation k (Fin 4) f at he
  rw [hz,map_zero] at he
  exact he.symm
end ActualPresentation

open CategoryTheory CategoryTheory.Limits NSP14.Homological
section FirstTor
variable (k : Type) [Field k] (I : Ideal (P k))
    (haug : I ≤ RingHom.ker (augmentation k (Fin 4)).toRingHom)

/-- Tor1 of a genuine augmented quotient is its genuine ideal's Nakayama fibre.
Neither the quotient nor the chain groups are required finite-dimensional over k. -/
noncomputable def firstIdealIso :
    koszulHomology k (Fin 4) (variableList k (Fin 4)) (NSP14.Endpoint.artinModule k (Fin 4) I) 1 ≅
      koszulHomology k (Fin 4) (variableList k (Fin 4)) (NSP14.Endpoint.artinIdealModule k (Fin 4) I) 0 := by
  have hz : (koszulHomologyFunctor k (Fin 4) (variableList k (Fin 4)) 0).map
      (NSP14.Endpoint.artinIdealInclusion k (Fin 4) I)=0 := by
    apply koszul_h0_map_zero_of_minimal
    intro a
    rw [polynomial_variable_submodule,variablesIdeal_all_eq_ker]
    exact haug a.property
  let hS := koszul_shortExact k (Fin 4) (variableList k (Fin 4))
    (NSP14.Endpoint.artinIdealSequence k (Fin 4) I) (NSP14.Endpoint.artinIdeal_shortExact k (Fin 4) I)
  let δ := hS.δ 1 0 rfl
  let : Mono δ := hS.mono_δ _ _ rfl (freeKoszulHomology_positive k (Fin 4)
    (ModuleCat.of (VariableRing k (Fin 4)) (VariableRing k (Fin 4))) 0)
  let : Epi δ := (hS.homology_exact₁ 1 0 rfl).epi_f_iff.mpr hz
  let := isIso_of_mono_of_epi δ
  exact asIso δ

include haug in
theorem first_generator_number :
    totalBetti k (Fin 4) (NSP14.Endpoint.artinModule k (Fin 4) I) 1=
      NSP14.Endpoint.idealGeneratorNumber k (Fin 4) I :=
  (((ModuleCat.restrictScalars (algebraMap k (VariableRing k (Fin 4)))).mapIso
    (firstIdealIso k I haug)).toLinearEquiv.finrank_eq)

include haug in
theorem first_le_generators {ι : Type} [Fintype ι] (v : ι → P k) (hI : I=Ideal.span (Set.range v)) :
    totalBetti k (Fin 4) (NSP14.Endpoint.artinModule k (Fin 4) I) 1 ≤ Fintype.card ι := by
  rw [first_generator_number k I haug]
  exact NSP14.Width.idealGeneratorNumber_le k (Fin 4) I v hI
end FirstTor
end NSP14.NarrowFour.WidthFour
