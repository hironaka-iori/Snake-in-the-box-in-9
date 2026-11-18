import CubeCut
import CutAxis237_001
import CutAxis237_002
import CutAxis237_004
import CutAxis237_008
import CutAxis237_016
import CutAxis237_032
import CutAxis237_064
import CutAxis237_128
import CutAxis237_256

set_option Elab.async false

namespace CutGeometry237
open CubeCut237

def Adj (u z : Nat) : Prop := ∃ i ∈ axes, z = u ^^^ i

private theorem back (u i : Nat) : (u ^^^ i) ^^^ i = u := by
  simp [Nat.xor_assoc]

private theorem commute_steps (u i j : Nat) : (u ^^^ i) ^^^ j = (u ^^^ j) ^^^ i := by
  rw [Nat.xor_assoc, Nat.xor_comm i j, ← Nat.xor_assoc]

private theorem same_mask {u i j a b : Nat}
    (h : (u ^^^ i) ^^^ j = (u ^^^ a) ^^^ b) : i ^^^ j = a ^^^ b := by
  rw [Nat.xor_assoc, Nat.xor_assoc] at h
  have eq := congrArg (fun x => u ^^^ x) h
  simpa only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] using eq

private theorem axis_masks :
    ∀ i ∈ axes, ∀ j ∈ axes, ∀ a ∈ axes, ∀ b ∈ axes,
      i < j → i ^^^ j = a ^^^ b → (i = a ∧ j = b) ∨ (i = b ∧ j = a) := by
  intro i hi
  simp only [axes, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CutAxis237.axis_001
  · exact CutAxis237.axis_002
  · exact CutAxis237.axis_004
  · exact CutAxis237.axis_008
  · exact CutAxis237.axis_016
  · exact CutAxis237.axis_032
  · exact CutAxis237.axis_064
  · exact CutAxis237.axis_128
  · exact CutAxis237.axis_256

theorem ordered_pair_unique {u i j a b : Nat}
    (hi : i ∈ axes) (hj : j ∈ axes) (ha : a ∈ axes) (hb : b ∈ axes)
    (ij : i < j) (ab : a < b)
    (h : (u ^^^ i) ^^^ j = (u ^^^ a) ^^^ b) : i = a ∧ j = b := by
  have mask := axis_masks i hi j hj a ha b hb ij (same_mask h)
  omega

theorem common_has_ordered_pair {u w z : Nat} (neq : u ≠ w)
    (uz : Adj u z) (wz : Adj w z) :
    ∃ i ∈ axes, ∃ j ∈ axes, i < j ∧ w = (u ^^^ i) ^^^ j := by
  obtain ⟨a, ha, za⟩ := uz
  obtain ⟨b, hb, zb⟩ := wz
  have endpt : (u ^^^ a) ^^^ b = w := by rw [←za, zb, back]
  have ne : a ≠ b := by
    intro eq
    rw [eq, back] at endpt
    exact neq endpt
  by_cases ab : a < b
  · exact ⟨a, ha, b, hb, ab, endpt.symm⟩
  · exact ⟨b, hb, a, ha, by omega, endpt.symm.trans (commute_steps u a b)⟩

/-- Both intermediate labels and no others can witness this partner.
The numeric bitset checker enumerates just these two possibilities. -/
theorem common_labels {u w i j : Nat} (hi : i ∈ axes) (hj : j ∈ axes)
    (ij : i < j) (endpt : w = (u ^^^ i) ^^^ j) (z : Nat) :
    (Adj u z ∧ Adj w z) ↔ z = u ^^^ i ∨ z = u ^^^ j := by
  constructor
  · rintro ⟨⟨a, ha, za⟩, ⟨b, hb, zb⟩⟩
    have eq : (u ^^^ i) ^^^ j = (u ^^^ a) ^^^ b := by
      rw [←endpt, ←za, zb, back]
    have pairs := axis_masks i hi j hj a ha b hb ij (same_mask eq)
    rcases pairs with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact Or.inl za
    · exact Or.inr za
  · rintro (rfl | rfl)
    · exact ⟨⟨i,hi,rfl⟩, ⟨j,hj, by rw [endpt, back]⟩⟩
    · exact ⟨⟨j,hj,rfl⟩, ⟨i,hi, by rw [endpt, commute_steps u i j, back]⟩⟩

private theorem one_bit (v x : Nat) : (bit v).testBit x = decide (v = x) := by
  simp [bit, Nat.one_shiftLeft, Nat.testBit_two_pow]

private theorem fold_bits (vs : List Nat) (f : Nat → Nat) (m x : Nat) :
    ((vs.foldl (fun mask i => mask ||| bit (f i)) m).testBit x = true) ↔
    m.testBit x = true ∨ ∃ i ∈ vs, f i = x := by
  induction vs generalizing m with
  | nil => simp
  | cons y ys ih =>
      simp [ih, one_bit, or_assoc]

theorem encoded_member (vs : List Nat) (x : Nat) :
    (encode vs).testBit x = true ↔ x ∈ vs := by
  change ((vs.foldl (fun mask i => mask ||| bit (id i)) 0).testBit x = true) ↔ _
  rw [fold_bits]
  simp

theorem neighbour_member (z x : Nat) : (neighbours z).testBit x = true ↔ Adj z x := by
  unfold neighbours Adj
  rw [fold_bits]
  simp [eq_comm]

theorem pair_mask_exact (selected z u w : Nat) :
    selected &&& neighbours z = bit u ||| bit w ↔
      ∀ x, (selected.testBit x = true ∧ Adj z x) ↔ (x = u ∨ x = w) := by
  have entry (x : Nat) :
      ((selected &&& neighbours z).testBit x = true ↔ (bit u ||| bit w).testBit x = true) ↔
      ((selected.testBit x = true ∧ Adj z x) ↔ x = u ∨ x = w) := by
    simp [neighbour_member, one_bit, @eq_comm Nat u x, @eq_comm Nat w x]
  constructor
  · intro h x
    exact (entry x).mp (by rw [h])
  · intro h
    apply Nat.eq_of_testBit_eq
    intro x
    have eq := (entry x).mpr (h x)
    cases lhs : (selected &&& neighbours z).testBit x <;>
      cases rhs : (bit u ||| bit w).testBit x <;> simp_all

#print axioms ordered_pair_unique
#print axioms common_has_ordered_pair
#print axioms common_labels
#print axioms encoded_member
#print axioms neighbour_member
#print axioms pair_mask_exact

end CutGeometry237
