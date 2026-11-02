import Mathlib.Tactic

namespace Snake9.GraphInterpretation75

/-- Base-six encoding used by the graph builder, with symbols one through six. -/
def encodeCounts : List Nat → Nat → Nat
  | [], acc => acc
  | a :: rest, acc => encodeCounts rest (acc * 6 + (a-1))

theorem six_count_code (a b c d e f : Nat)
    (ha : 1 ≤ a ∧ a ≤ 6) (hb : 1 ≤ b ∧ b ≤ 6)
    (hc : 1 ≤ c ∧ c ≤ 6) (hd : 1 ≤ d ∧ d ≤ 6)
    (he : 1 ≤ e ∧ e ≤ 6) (hf : 1 ≤ f ∧ f ≤ 6) :
    encodeCounts [a,b,c,d,e,f] 0 < 46656 ∧
    encodeCounts [a,b,c,d,e,f] 0 / 6 = encodeCounts [a,b,c,d,e] 0 ∧
    encodeCounts [a,b,c,d,e,f] 0 % 7776 = encodeCounts [b,c,d,e,f] 0 ∧
    encodeCounts [a,b,c,d,e,f] 0 % 6 + 1 = f := by
  simp only [encodeCounts]
  omega

theorem five_count_code (a b c d e : Nat)
    (ha : 1 ≤ a ∧ a ≤ 6) (hb : 1 ≤ b ∧ b ≤ 6)
    (hc : 1 ≤ c ∧ c ≤ 6) (hd : 1 ≤ d ∧ d ≤ 6)
    (he : 1 ≤ e ∧ e ≤ 6) : encodeCounts [a,b,c,d,e] 0 < 7776 := by
  simp only [encodeCounts]
  omega

/-- The history-zero states retain a direction-shape index; nonzero history
states store their compatible direction shape implicitly. -/
def stateCode (shape history counts : Nat) : Nat :=
  if history = 0 then shape * 7776 + counts
  else 1026432 + (history-1) * 7776 + counts

theorem stateCode_lt (shape history counts : Nat)
    (hs : shape < 132) (hh : history < 75) (hc : counts < 7776) :
    stateCode shape history counts < 1601856 := by
  unfold stateCode
  split_ifs <;> omega

theorem stateCode_count_remainder (shape history counts : Nat)
    (hc : counts < 7776) : stateCode shape history counts % 7776 = counts := by
  unfold stateCode
  split_ifs <;> omega

theorem zero_history_shape (shape counts : Nat) (hc : counts < 7776) :
    stateCode shape 0 counts / 7776 = shape := by
  change (shape * 7776 + counts) / 7776 = shape
  omega

theorem nonzero_history_block (shape history counts : Nat)
    (hh : 0 < history) (hc : counts < 7776) :
    (stateCode shape history counts - 1026432) / 7776 + 1 = history := by
  simp only [stateCode, if_neg (by omega : history ≠ 0)]
  omega

/-- A capped guard below six is an exact guard on the original count. -/
theorem truncated_guard (a cap : Nat) (hcap : cap < 6) :
    min 6 a ≤ cap ↔ a ≤ cap := by omega

theorem unsaturated_exact (a : Nat) (h : min 6 a < 6) : min 6 a = a := by omega

theorem saturated_interval (a : Nat) (hbound : a ≤ 21) :
    min 6 a = 6 ↔ 6 ≤ a ∧ a ≤ 21 := by omega

#print axioms six_count_code
#print axioms five_count_code
#print axioms stateCode_lt
#print axioms stateCode_count_remainder
#print axioms zero_history_shape
#print axioms nonzero_history_block
#print axioms truncated_guard
#print axioms unsaturated_exact
#print axioms saturated_interval
end Snake9.GraphInterpretation75
