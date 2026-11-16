module

import NSP14.Combinatorics.Sidon

open NSP14 NSP14.Ordinary.SmallScalar

-- Sharp cyclic example and a composite-modulus example.
example : IsSidon ({0, 1, 3} : Finset (ZMod 7)) := by unfold IsSidon; decide
example : IsSidon ({0, 1, 3} : Finset (ZMod 8)) := by unfold IsSidon; decide
-- Squares/repeated summands must be included in the Sidon condition.
example : ¬IsSidon ({0, 1} : Finset (ZMod 2)) := by unfold IsSidon; decide

-- Universal impossibility at all three bad corners, not an enumeration of B.
example (B : Finset (ZMod 28)) (hc : B.card = 7) : ¬IsSidon B := by
  intro h
  have hbound := sidon_card_bound 28 B h
  rw [hc] at hbound
  norm_num at hbound
example (B : Finset (ZMod 36)) (hc : B.card = 8) : ¬IsSidon B := by
  intro h
  have hbound := sidon_card_bound 36 B h
  rw [hc] at hbound
  norm_num at hbound
example (B : Finset (ZMod 45)) (hc : B.card = 9) : ¬IsSidon B := by
  intro h
  have hbound := sidon_card_bound 45 B h
  rw [hc] at hbound
  norm_num at hbound

-- An interior point needs no Sidon witness at all.
example : 0 < gap 6 (cutoff 6) ((6 : ℚ) + 1 + 1) (triangular 6 + 0) := by
  apply small_gap_pos_of_boundary_sidon 29 6 1 0 (by decide) (by decide)
  intro _ h
  omega

-- The witness interface yields the full sharp multiplicity/deficit bounds.
example {S : AddSubmonoid ℕ} {m e d : ℕ} [NeZero m]
    (D : AperyPairData S m e) (he : 1 ≤ e) (hm : m = e + d) :
    (e - 1)^2 ≤ d := D.deficit_bound d he hm

#print axioms sidon_difference_injective
#print axioms sidon_card_bound
#print axioms apery_min_unique
#print axioms AperyPairData.residue_injective
#print axioms AperyPairData.residues_card
#print axioms AperyPairData.residues_sidon
#print axioms AperyPairData.multiplicity_bound
#print axioms AperyPairData.deficit_bound
#print axioms corner_condition_of_sidon
#print axioms small_gap_pos_of_sidon
#print axioms corner_condition_of_boundary_sidon
#print axioms small_gap_pos_of_boundary_sidon
#print axioms scalar_lt_of_boundary_sidon
#print axioms small_gap_pos_of_apery_pairs
