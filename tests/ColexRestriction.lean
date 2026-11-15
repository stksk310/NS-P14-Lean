module
public import NSP14.Lex.ColexRestriction
@[expose] public section
open scoped Classical
namespace NSP14.Tests.ColexRestriction

theorem actual_colex_zero_count {n r : ℕ} (F L : Finset (Finset (Fin (n+1)))) (hr : 1≤r)
    (hF : (F : Set (Finset (Fin (n+1)))).Sized r) (hL : Finset.Colex.IsInitSeg L r)
    (hcard : L.card≤F.card)
    (hshift : ∀ A∈F,(0 : Fin (n+1))∉A → ∀ x∈A,insert 0 (A.erase x)∈F) :
    (L.filter (fun A => (0 : Fin (n+1))∈A)).card≤(F.filter (fun A => (0 : Fin (n+1))∈A)).card :=
  NSP14.Lex.colex_zero_mem_card_le F L hr hF hL hcard hshift
end NSP14.Tests.ColexRestriction
