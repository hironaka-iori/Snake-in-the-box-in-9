import LocalWindowBridge

namespace Snake9.MissingPair134
open Snake9.LocalWindow

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

-- This finite identity ranges over four coordinates, hence only 9^4 choices.
-- It does not enumerate vertices or assume anything about a snake.
private theorem common_flip_cases :
    ∀ b c d e : Fin 9, b ≠ c →
      2 ^ c.val = (2 ^ b.val ^^^ 2 ^ d.val) ^^^ 2 ^ e.val →
      d = b ∨ d = c := by
  decide

/-- Away from the normalized endpoint, the two consecutive pairs force their
triple between them and forbid the remaining pair throughout the snake. -/
theorem middle_and_missing_pair {m : Nat} (p : Snake m)
    (j a b c : Nat) (hj : 2 ≤ j) (hjm : j + 2 ≤ m)
    (ha : a < 9) (hb : b < 9) (hc : c < 9)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hzero : vx p 0 = 0)
    (hleft : vx p j = 2 ^ a ^^^ 2 ^ b)
    (hright : vx p (j + 2) = 2 ^ a ^^^ 2 ^ c) :
    vx p (j + 1) = (2 ^ a ^^^ 2 ^ b) ^^^ 2 ^ c ∧
      ∀ k, k ≤ m → vx p k ≠ 2 ^ b ^^^ 2 ^ c := by
  have hmid : vx p (j + 1) = (2 ^ a ^^^ 2 ^ b) ^^^ 2 ^ c := by
    obtain ⟨d, hd, hfirst⟩ :=
      (vx_adj_iff p (i := j) (j := j + 1) (by omega) (by omega)).2
        (Or.inl rfl)
    obtain ⟨e, he, hsecond⟩ :=
      (vx_adj_iff p (i := j + 1) (j := j + 2) (by omega) (by omega)).2
        (Or.inl (by omega))
    rw [hfirst, hleft, hright] at hsecond
    have hcancel : 2 ^ c = (2 ^ b ^^^ 2 ^ d) ^^^ 2 ^ e := by
      apply xor_left_inj (2 ^ a)
      simpa only [Nat.xor_assoc] using hsecond
    have hbc' : (⟨b, hb⟩ : Fin 9) ≠ ⟨c, hc⟩ := by
      intro h
      exact hbc (congrArg Fin.val h)
    rcases common_flip_cases ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ ⟨e, he⟩ hbc' hcancel with
      hdb | hdc
    · have hd' : d = b := congrArg Fin.val hdb
      have hunit : vx p (j + 1) = 2 ^ a := by
        rw [hfirst, hleft, hd']
        simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      have hadj :=
        (vx_adj_iff p (i := 0) (j := j + 1) (by omega) (by omega)).1
          ⟨a, ha, by rw [hunit, hzero, Nat.zero_xor]⟩
      omega
    · have hd' : d = c := congrArg Fin.val hdc
      simpa only [hleft, hd'] using hfirst
  refine ⟨hmid, ?_⟩
  intro k hk hselected
  have hadj : ∃ d, d < 9 ∧ vx p k = vx p (j + 1) ^^^ 2 ^ d := by
    refine ⟨a, ha, ?_⟩
    rw [hselected, hmid, Nat.xor_assoc (2 ^ a) (2 ^ b) (2 ^ c),
      Nat.xor_comm (2 ^ a ^^^ (2 ^ b ^^^ 2 ^ c)) (2 ^ a),
      ← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor]
  have hpositions :=
    (vx_adj_iff p (i := j + 1) (j := k) (by omega) hk).1 hadj
  have hkcases : k = j ∨ k = j + 2 := by omega
  rcases hkcases with hkj | hkj
  · subst k
    apply hac
    apply pow_two_inj
    apply xor_left_inj (2 ^ b)
    calc
      2 ^ b ^^^ 2 ^ a = 2 ^ a ^^^ 2 ^ b := Nat.xor_comm _ _
      _ = vx p j := hleft.symm
      _ = 2 ^ b ^^^ 2 ^ c := hselected
  · subst k
    apply hab
    apply pow_two_inj
    apply xor_left_inj (2 ^ c)
    calc
      2 ^ c ^^^ 2 ^ a = 2 ^ a ^^^ 2 ^ c := Nat.xor_comm _ _
      _ = vx p (j + 2) := hright.symm
      _ = 2 ^ b ^^^ 2 ^ c := hselected
      _ = 2 ^ c ^^^ 2 ^ b := Nat.xor_comm _ _

#print axioms middle_and_missing_pair
end Snake9.MissingPair134
