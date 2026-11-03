import DfsParity
import ActualEndpoint122
import ActualPair121

namespace Snake9.OddPair130
open Snake9.LocalWindow Snake9.WindowAutomaton Snake9.DirectionWindow
open Snake9.Guards79 Snake9.EndpointGeometry122

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem countP_xor_mod_two {α : Type} (xs : List α) (f g : α → Bool) :
    (xs.countP (fun x => f x ^^ g x)) % 2 =
      (xs.countP f + xs.countP g) % 2 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases hf : f a <;> cases hg : g a <;>
      simp_all [List.countP_cons] <;> omega

theorem bitParity_xor (u v : Nat) :
    bitParity (u ^^^ v) = (bitParity u ^^ bitParity v) := by
  simp only [bitParity, Nat.testBit_xor]
  rw [countP_xor_mod_two]
  rcases Nat.mod_two_eq_zero_or_one
      ((List.range 9).countP (fun k => u.testBit k)) with hu | hu <;>
    rcases Nat.mod_two_eq_zero_or_one
      ((List.range 9).countP (fun k => v.testBit k)) with hv | hv <;>
    simp [Nat.add_mod, hu, hv]

theorem hamming_two_same_parity (u v : Nat) (h : hamming u v = 2) :
    bitParity u = bitParity v := by
  have hx : bitParity (u ^^^ v) = false := by
    change (hamming u v % 2 == 1) = false
    rw [h]
    rfl
  rw [bitParity_xor] at hx
  cases hu : bitParity u <;> cases hv : bitParity v <;> simp_all

theorem equality_even_length_and_start {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (heq : coreAlpha p (r+2) + coreAlpha p (r+4) = 8) :
    m % 2 = 0 ∧ r % 2 = 0 := by
  have he := ActualEndpoint122.actual_equality_endpoints p r hr hshape heq
  have h0 := hamming_two_same_parity _ _ (he 0 (Or.inl rfl)).1
  have hm := hamming_two_same_parity _ _ (he m (Or.inr rfl)).1
  have hend : bitParity (vx p m) = bitParity (vx p 0) := hm.symm.trans h0
  have h0pos : 0 < m+1 := by omega
  have hrpos : r+2 < m+1 := by omega
  have hmpos : m < m+1 := by omega
  have hp : bitParity (vx p (r+2)) =
      (bitParity (vx p 0) ^^ ((r+2) % 2 == 1)) := by
    simpa only [vx, dif_pos hrpos, dif_pos h0pos] using
      (parity_along p (r+2) (by omega))
  have hep : bitParity (vx p m) =
      (bitParity (vx p 0) ^^ (m % 2 == 1)) := by
    simpa only [vx, dif_pos hmpos, dif_pos h0pos] using endpoint_parity p
  rw [h0] at hp
  rw [hend] at hep
  have hmeven : m % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · exact h
    · cases hb : bitParity (vx p 0) <;> simp [h,hb] at hep
  have hreven : (r+2) % 2 = 0 := by
    rcases Nat.mod_two_eq_zero_or_one (r+2) with h | h
    · exact h
    · cases hb : bitParity (vx p 0) <;> simp [h,hb] at hp
  exact ⟨hmeven,by omega⟩

theorem pair_lower_nine_of_odd_length_or_start {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2])
    (hodd : m % 2 = 1 ∨ r % 2 = 1) :
    9 ≤ coreAlpha p (r+2) + coreAlpha p (r+4) := by
  have h8 := ActualPair121.actual_pair_sum p r hr hshape
  by_contra hn
  have heq : coreAlpha p (r+2) + coreAlpha p (r+4) = 8 := by omega
  obtain ⟨hm,hr'⟩ := equality_even_length_and_start p r hr hshape heq
  rcases hodd with hodd | hodd <;> omega

theorem pair_lower_nine_of_odd_length {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2]) (hodd : m % 2 = 1) :
    9 ≤ coreAlpha p (r+2) + coreAlpha p (r+4) :=
  pair_lower_nine_of_odd_length_or_start p r hr hshape (Or.inl hodd)

theorem pair_lower_nine_of_odd_start {m : Nat} (p : Snake m) (r : Nat)
    (hr : r+6 ≤ m)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2]) (hodd : r % 2 = 1) :
    9 ≤ coreAlpha p (r+2) + coreAlpha p (r+4) :=
  pair_lower_nine_of_odd_length_or_start p r hr hshape (Or.inr hodd)

theorem pair_lower_nine_length235 (p : Snake 235) (r : Nat)
    (hr : r+6 ≤ 235)
    (hshape : canon (dsOf p r 6) = [0,1,2,0,3,2]) :
    9 ≤ coreAlpha p (r+2) + coreAlpha p (r+4) :=
  pair_lower_nine_of_odd_length p r hr hshape (by decide)

#print axioms countP_xor_mod_two
#print axioms bitParity_xor
#print axioms hamming_two_same_parity
#print axioms equality_even_length_and_start
#print axioms pair_lower_nine_of_odd_length_or_start
#print axioms pair_lower_nine_of_odd_length
#print axioms pair_lower_nine_of_odd_start
#print axioms pair_lower_nine_length235
end Snake9.OddPair130
