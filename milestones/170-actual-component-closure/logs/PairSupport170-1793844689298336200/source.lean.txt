import CubeLocal

set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace Snake9.PairSupport170

-- A three-coordinate certificate, rather than a four-coordinate equality table.
private theorem pair_bit_support (a b k : Coord) (hab : a ≠ b) :
    ((pair a b).val.testBit k.val = true ↔ k = a ∨ k = b) := by
  change ((2^a.val ^^^ 2^b.val).testBit k.val = true ↔ k = a ∨ k = b)
  rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow]
  simp only [Fin.val_inj]
  by_cases hka : k = a
  · subst k
    simp [hab, Ne.symm hab]
  · by_cases hkb : k = b
    · subst k
      simp [hab, Ne.symm hab]
    · simp [hka, hkb, Ne.symm hka, Ne.symm hkb]

theorem pair_support_unique (a b c d : Coord)
    (hab : a ≠ b) (hcd : c ≠ d) (he : pair a b = pair c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hbit : (pair a b).val.testBit a.val = true :=
    (pair_bit_support a b a hab).mpr (Or.inl rfl)
  have hcbit : (pair c d).val.testBit a.val = true := by
    rw [← he]
    exact hbit
  rcases (pair_bit_support c d a hcd).mp hcbit with hac | had
  · subst c
    exact Or.inl ⟨rfl, pair_injective_right a b d he⟩
  · subst d
    have he' : pair a b = pair a c := he.trans (pair_comm c a)
    exact Or.inr ⟨rfl, pair_injective_right a b c he'⟩

private def parityBits : List Nat → Nat → Bool
  | [], _ => false
  | k :: ks, n => n.testBit k ^^ parityBits ks n

private theorem parity_xor (ks : List Nat) (u v : Nat) :
    parityBits ks (u ^^^ v) = (parityBits ks u ^^ parityBits ks v) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    simp only [parityBits, Nat.testBit_xor, ih]
    have exchange : ∀ a b c d : Bool, ((a ^^ b) ^^ (c ^^ d)) = ((a ^^ c) ^^ (b ^^ d)) := by decide
    exact exchange _ _ _ _

private def bitParity (v : Vertex) : Bool := parityBits (List.range 9) v.val

private theorem unit_parity : ∀ a : Coord, bitParity (unit a) = true := by decide

private theorem pair_parity (a b : Coord) : bitParity (pair a b) = false := by
  change parityBits (List.range 9) ((unit a).val ^^^ (unit b).val) = false
  rw [parity_xor]
  change (bitParity (unit a) ^^ bitParity (unit b)) = false
  rw [unit_parity, unit_parity]
  rfl

private theorem triple_parity (a b k : Coord) : bitParity (triple a b k) = true := by
  change parityBits (List.range 9) ((pair a b).val ^^^ (unit k).val) = true
  rw [parity_xor]
  change (bitParity (pair a b) ^^ bitParity (unit k)) = true
  rw [pair_parity, unit_parity]
  rfl

theorem pair_not_adjacent (a b c d : Coord) : ¬ Adj (pair a b) (pair c d) := by
  intro hadj
  obtain ⟨k, he⟩ := neighbor_pair a b hadj
  have hp := pair_parity c d
  have ht := triple_parity a b k
  rw [he] at hp
  rw [ht] at hp
  cases hp

#print axioms pair_support_unique
#print axioms pair_not_adjacent

end Snake9.PairSupport170
