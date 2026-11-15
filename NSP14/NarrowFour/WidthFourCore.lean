module
public import NSP14.NarrowFour.SmallWidths
public import Mathlib.Tactic.FinCases
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
namespace NSP14.NarrowFour.WidthFour

def anchorC (i : Fin 5) : ℕ := match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 1 | _ => 2
def anchorN (i : Fin 5) : ℕ := match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | _ => 6
def anchorY (i : Fin 5) : ℕ := match i.val with | 1 => 1 | 2 => 2 | _ => 0
def anchorZ (i : Fin 5) : ℕ := match i.val with | 3 => 1 | 4 => 2 | _ => 0

theorem anchor_degree (i : Fin 5) : anchorY i+anchorZ i=anchorC i := by fin_cases i <;> decide
theorem anchor_offset (i : Fin 5) : anchorY i+3*anchorZ i=anchorN i := by fin_cases i <;> decide
theorem anchor_bound (i : Fin 5) : anchorN i ≤ 4*anchorC i := by fin_cases i <;> decide

/-- Four free columns and one x-free column; the restriction is part of the type. -/
structure Column where
  anchor : Fin 5
  L : ℕ
  K : ℕ
  restricted : anchor=4 → L=0

def Column.degree (p : Column) : ℕ := p.L+p.K+anchorC p.anchor
def Column.offset (p : Column) : ℕ := anchorN p.anchor+4*p.K

theorem column_injective : Function.Injective (fun p : Column => (p.degree,p.offset)) := by
  rintro ⟨i,L,K,hr⟩ ⟨j,M,H,hs⟩ he
  have hd := congrArg Prod.fst he
  have hn := congrArg Prod.snd he
  change L+K+anchorC i=M+H+anchorC j at hd
  change anchorN i+4*K=anchorN j+4*H at hn
  fin_cases i <;> fin_cases j <;> simp [anchorC,anchorN] at hd hn hr hs
  all_goals first
    | omega
    | have hL : L=M := by omega
      have hK : K=H := by omega
      subst M;subst H;simp_all

def Admissible (degree offset : ℕ) : Prop := offset ≤ 4*degree ∧ ¬(degree=1 ∧ offset=2)

theorem column_exists (degree offset : ℕ) (ha : Admissible degree offset) :
    ∃ p : Column, p.degree=degree ∧ p.offset=offset := by
  have hm := Nat.mod_add_div offset 4
  have hr := Nat.mod_lt offset (by omega : 0<4)
  obtain ⟨hb,hole⟩ := ha
  have hcases : offset%4=0 ∨ offset%4=1 ∨ offset%4=2 ∨ offset%4=3 := by omega
  rcases hcases with h|h|h|h
  · refine ⟨⟨0,degree-offset/4,offset/4,by simp⟩,?_,?_⟩
    · norm_num [Column.degree,anchorC];omega
    · norm_num [Column.offset,anchorN];omega
  · refine ⟨⟨1,degree-offset/4-1,offset/4,by simp⟩,?_,?_⟩
    · norm_num [Column.degree,anchorC];omega
    · norm_num [Column.offset,anchorN];omega
  · by_cases hd : offset/4+2 ≤ degree
    · refine ⟨⟨2,degree-offset/4-2,offset/4,by simp⟩,?_,?_⟩
      · norm_num [Column.degree,anchorC];omega
      · norm_num [Column.offset,anchorN];omega
    · refine ⟨⟨4,0,offset/4-1,by intro _;rfl⟩,?_,?_⟩
      · norm_num [Column.degree,anchorC];omega
      · norm_num [Column.offset,anchorN];omega
  · refine ⟨⟨3,degree-offset/4-1,offset/4,by simp⟩,?_,?_⟩
    · norm_num [Column.degree,anchorC];omega
    · norm_num [Column.offset,anchorN];omega

variable (D : Endpoint.Data)
def y (ha : D.a={1,3}) : D.a := ⟨1,by rw [ha];decide⟩
def z (ha : D.a={1,3}) : D.a := ⟨3,by rw [ha];decide⟩

def columnPoint (ha : D.a={1,3}) (p : Column) : D.corePoints :=
  D.coreEndpointPoint (p.L,p.K)+word D (y D ha) (z D ha) (anchorY p.anchor) (anchorZ p.anchor)

theorem columnPoint_coe (hu : D.u=4) (ha : D.a={1,3}) (p : Column) :
    (columnPoint D ha p).val=(p.degree,p.offset) := by
  change (D.coreEndpointPoint (p.L,p.K)).val+
    (word D (y D ha) (z D ha) (anchorY p.anchor) (anchorZ p.anchor)).val=_
  rw [D.coreEndpointPoint_coe,word_coe]
  dsimp [y,z,Column.degree,Column.offset]
  rw [hu]
  have hd := anchor_degree p.anchor
  have hn := anchor_offset p.anchor
  apply Prod.ext <;> dsimp <;> omega

theorem columnPoint_injective (hu : D.u=4) (ha : D.a={1,3}) : Function.Injective (columnPoint D ha) := by
  intro p q he
  apply column_injective
  simpa only [columnPoint_coe D hu ha] using congrArg (fun z : D.corePoints => z.val) he



theorem corePoint_admissible (hu : D.u=4) (ha : D.a={1,3}) (p : D.corePoints) :
    Admissible p.val.1 p.val.2 := by
  have hb := D.corePoint_bound p.property
  change p.val.2 ≤ D.u*p.val.1 at hb
  rw [hu] at hb
  refine ⟨hb,?_⟩
  rintro ⟨hd,hn⟩
  obtain ⟨w,hw⟩ := D.exists_coreWord p
  have hlen := D.coreWord_degree w
  rw [hw] at hlen
  change p.val.1=w.length at hlen
  rw [hd] at hlen
  obtain ⟨g,hg⟩ := List.length_eq_one_iff.mp hlen.symm
  have hoff := D.coreWord_offset w
  rw [hw,hg] at hoff
  change p.val.2=g.val+0 at hoff
  have hval : g.val=2 := by omega
  rcases (D.mem_offsets g.val).mp g.property with h0|h4|h13
  · omega
  · omega
  · rw [ha] at h13
    have h13' : g.val=1 ∨ g.val=3 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using h13
    omega

theorem columnPoint_surjective (hu : D.u=4) (ha : D.a={1,3}) : Function.Surjective (columnPoint D ha) := by
  intro p
  obtain ⟨c,hc⟩ := column_exists p.val.1 p.val.2 (corePoint_admissible D hu ha p)
  refine ⟨c,?_⟩
  apply Subtype.ext
  rw [columnPoint_coe D hu ha]
  exact Prod.ext hc.1 hc.2

noncomputable def columnEquiv (hu : D.u=4) (ha : D.a={1,3}) : Column ≃ D.corePoints :=
  Equiv.ofBijective (columnPoint D ha) ⟨columnPoint_injective D hu ha,columnPoint_surjective D hu ha⟩

/-- Actual core monomials, not just a numerical Hilbert-function model. -/
noncomputable def columnBasis (k : Type) [Field k] (hu : D.u=4) (ha : D.a={1,3}) :
    Module.Basis Column k (D.Core k) := (AddMonoidAlgebra.basis D.corePoints k).reindex (columnEquiv D hu ha).symm

theorem columnBasis_apply (k : Type) [Field k] (hu : D.u=4) (ha : D.a={1,3}) (p : Column) :
    columnBasis D k hu ha p=D.coreMonomial k (columnPoint D ha p) := by
  rw [columnBasis,Module.Basis.reindex_apply,AddMonoidAlgebra.basis_apply]
  rfl
end NSP14.NarrowFour.WidthFour
