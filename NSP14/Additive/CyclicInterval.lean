module
public import NSP14.Additive.ConnectedSequence
@[expose] public section
open scoped Pointwise BigOperators
namespace NSP14.Additive
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
def cyclicInterval (a : G) (S : ℕ) : Finset G :=
  (Finset.range (S+1)).image (fun n => n • a)
theorem mem_cyclicInterval (a : G) (S : ℕ) (x : G) :
    x ∈ cyclicInterval a S ↔ ∃ n ≤ S, n • a = x := by
  simp only [cyclicInterval,Finset.mem_image,Finset.mem_range,Nat.lt_succ_iff]
@[simp] theorem cyclicInterval_one (a : G) : cyclicInterval a 1 = {0,a} := by
  simp only [cyclicInterval,show Finset.range 2 = {0,1} from rfl,Finset.image_insert,
    Finset.image_singleton,zero_nsmul,one_nsmul]

theorem cyclicInterval_union (a : G) (S k : ℕ) (hk : k ≤ S+1) :
    cyclicInterval a S ∪ (k • a +ᵥ cyclicInterval a S) = cyclicInterval a (S+k) := by
  ext x
  simp only [Finset.mem_union,Finset.mem_vadd_finset,mem_cyclicInterval]
  constructor
  · rintro (hx | ⟨y,hy,he⟩)
    · obtain ⟨n,hn,rfl⟩ := hx
      exact ⟨n,by omega,rfl⟩
    · obtain ⟨n,hn,rfl⟩ := hy
      exact ⟨k+n,by omega,by simpa only [add_nsmul,vadd_eq_add] using he⟩
  · rintro ⟨n,hn,rfl⟩
    by_cases hnS : n ≤ S
    · exact Or.inl ⟨n,hnS,rfl⟩
    · right
      refine ⟨(n-k) • a,⟨n-k,by omega,rfl⟩,?_⟩
      change k • a + (n-k) • a = n • a
      rw [←add_nsmul,Nat.add_sub_of_le (by omega : k ≤ n)]
end NSP14.Additive
