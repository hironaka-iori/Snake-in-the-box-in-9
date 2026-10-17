import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec55 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1761 (q : Nat → Bool) : valuationOf q 1099 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1132 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1099)) (literal (valuationOf q) (1123)) (literal (valuationOf q) (1132)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 1 1 (meaning1099 q) (meaning1123 q) (meaning1132 q) hs
  change valuationOf q 1099 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1132 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1761 (q : Snake 81) (h : Conditions q) : valuation q 1099 = false ∨ valuation q 1123 = false ∨ valuation q 1132 = true := counterClause1761 (baseVal q)

theorem counterClause1762 (q : Nat → Bool) : valuationOf q 1099 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1133 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1099)) (literal (valuationOf q) (1124)) (literal (valuationOf q) (1133)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 1 2 (meaning1099 q) (meaning1124 q) (meaning1133 q) hs
  change valuationOf q 1099 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1133 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1762 (q : Snake 81) (h : Conditions q) : valuation q 1099 = false ∨ valuation q 1124 = false ∨ valuation q 1133 = true := counterClause1762 (baseVal q)

theorem counterClause1763 (q : Nat → Bool) : valuationOf q 1099 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1134 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1099)) (literal (valuationOf q) (1125)) (literal (valuationOf q) (1134)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 1 3 (meaning1099 q) (meaning1125 q) (meaning1134 q) hs
  change valuationOf q 1099 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1134 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1763 (q : Snake 81) (h : Conditions q) : valuation q 1099 = false ∨ valuation q 1125 = false ∨ valuation q 1134 = true := counterClause1763 (baseVal q)

theorem counterClause1764 (q : Nat → Bool) : valuationOf q 1099 = false ∨ valuationOf q 1126 = false ∨ valuationOf q 1135 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1099)) (literal (valuationOf q) (1126)) (literal (valuationOf q) (1135)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 1 4 (meaning1099 q) (meaning1126 q) (meaning1135 q) hs
  change valuationOf q 1099 = false ∨ valuationOf q 1126 = false ∨ valuationOf q 1135 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1764 (q : Snake 81) (h : Conditions q) : valuation q 1099 = false ∨ valuation q 1126 = false ∨ valuation q 1135 = true := counterClause1764 (baseVal q)

theorem counterClause1765 (q : Nat → Bool) : valuationOf q 1100 = false ∨ valuationOf q 1132 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1100)) (literal (valuationOf q) (1132)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 2 (meaning1100 q) (meaning1132 q) hs
  change valuationOf q 1100 = false ∨ valuationOf q 1132 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1765 (q : Snake 81) (h : Conditions q) : valuation q 1100 = false ∨ valuation q 1132 = true := counterClause1765 (baseVal q)

theorem counterClause1766 (q : Nat → Bool) : valuationOf q 1100 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1133 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1100)) (literal (valuationOf q) (1123)) (literal (valuationOf q) (1133)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 2 1 (meaning1100 q) (meaning1123 q) (meaning1133 q) hs
  change valuationOf q 1100 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1133 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1766 (q : Snake 81) (h : Conditions q) : valuation q 1100 = false ∨ valuation q 1123 = false ∨ valuation q 1133 = true := counterClause1766 (baseVal q)

theorem counterClause1767 (q : Nat → Bool) : valuationOf q 1100 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1134 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1100)) (literal (valuationOf q) (1124)) (literal (valuationOf q) (1134)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 2 2 (meaning1100 q) (meaning1124 q) (meaning1134 q) hs
  change valuationOf q 1100 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1134 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1767 (q : Snake 81) (h : Conditions q) : valuation q 1100 = false ∨ valuation q 1124 = false ∨ valuation q 1134 = true := counterClause1767 (baseVal q)

theorem counterClause1768 (q : Nat → Bool) : valuationOf q 1100 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1135 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1100)) (literal (valuationOf q) (1125)) (literal (valuationOf q) (1135)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 2 3 (meaning1100 q) (meaning1125 q) (meaning1135 q) hs
  change valuationOf q 1100 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1135 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1768 (q : Snake 81) (h : Conditions q) : valuation q 1100 = false ∨ valuation q 1125 = false ∨ valuation q 1135 = true := counterClause1768 (baseVal q)

theorem counterClause1769 (q : Nat → Bool) : valuationOf q 1100 = false ∨ valuationOf q 1126 = false ∨ valuationOf q 1136 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1100)) (literal (valuationOf q) (1126)) (literal (valuationOf q) (1136)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 2 4 (meaning1100 q) (meaning1126 q) (meaning1136 q) hs
  change valuationOf q 1100 = false ∨ valuationOf q 1126 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1769 (q : Snake 81) (h : Conditions q) : valuation q 1100 = false ∨ valuation q 1126 = false ∨ valuation q 1136 = true := counterClause1769 (baseVal q)

theorem counterClause1770 (q : Nat → Bool) : valuationOf q 1101 = false ∨ valuationOf q 1133 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1101)) (literal (valuationOf q) (1133)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 3 (meaning1101 q) (meaning1133 q) hs
  change valuationOf q 1101 = false ∨ valuationOf q 1133 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1770 (q : Snake 81) (h : Conditions q) : valuation q 1101 = false ∨ valuation q 1133 = true := counterClause1770 (baseVal q)

theorem counterClause1771 (q : Nat → Bool) : valuationOf q 1101 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1134 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1101)) (literal (valuationOf q) (1123)) (literal (valuationOf q) (1134)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 3 1 (meaning1101 q) (meaning1123 q) (meaning1134 q) hs
  change valuationOf q 1101 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1134 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1771 (q : Snake 81) (h : Conditions q) : valuation q 1101 = false ∨ valuation q 1123 = false ∨ valuation q 1134 = true := counterClause1771 (baseVal q)

theorem counterClause1772 (q : Nat → Bool) : valuationOf q 1101 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1135 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1101)) (literal (valuationOf q) (1124)) (literal (valuationOf q) (1135)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 3 2 (meaning1101 q) (meaning1124 q) (meaning1135 q) hs
  change valuationOf q 1101 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1135 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1772 (q : Snake 81) (h : Conditions q) : valuation q 1101 = false ∨ valuation q 1124 = false ∨ valuation q 1135 = true := counterClause1772 (baseVal q)

theorem counterClause1773 (q : Nat → Bool) : valuationOf q 1101 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1136 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1101)) (literal (valuationOf q) (1125)) (literal (valuationOf q) (1136)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 3 3 (meaning1101 q) (meaning1125 q) (meaning1136 q) hs
  change valuationOf q 1101 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1773 (q : Snake 81) (h : Conditions q) : valuation q 1101 = false ∨ valuation q 1125 = false ∨ valuation q 1136 = true := counterClause1773 (baseVal q)

theorem counterClause1774 (q : Nat → Bool) : valuationOf q 1101 = false ∨ valuationOf q 1126 = false ∨ valuationOf q 1137 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1101)) (literal (valuationOf q) (1126)) (literal (valuationOf q) (1137)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 3 4 (meaning1101 q) (meaning1126 q) (meaning1137 q) hs
  change valuationOf q 1101 = false ∨ valuationOf q 1126 = false ∨ valuationOf q 1137 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1774 (q : Snake 81) (h : Conditions q) : valuation q 1101 = false ∨ valuation q 1126 = false ∨ valuation q 1137 = true := counterClause1774 (baseVal q)

theorem counterClause1775 (q : Nat → Bool) : valuationOf q 1102 = false ∨ valuationOf q 1134 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1102)) (literal (valuationOf q) (1134)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 4 (meaning1102 q) (meaning1134 q) hs
  change valuationOf q 1102 = false ∨ valuationOf q 1134 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1775 (q : Snake 81) (h : Conditions q) : valuation q 1102 = false ∨ valuation q 1134 = true := counterClause1775 (baseVal q)

theorem counterClause1776 (q : Nat → Bool) : valuationOf q 1102 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1135 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1102)) (literal (valuationOf q) (1123)) (literal (valuationOf q) (1135)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 4 1 (meaning1102 q) (meaning1123 q) (meaning1135 q) hs
  change valuationOf q 1102 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1135 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1776 (q : Snake 81) (h : Conditions q) : valuation q 1102 = false ∨ valuation q 1123 = false ∨ valuation q 1135 = true := counterClause1776 (baseVal q)

theorem counterClause1777 (q : Nat → Bool) : valuationOf q 1102 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1136 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1102)) (literal (valuationOf q) (1124)) (literal (valuationOf q) (1136)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 4 2 (meaning1102 q) (meaning1124 q) (meaning1136 q) hs
  change valuationOf q 1102 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1777 (q : Snake 81) (h : Conditions q) : valuation q 1102 = false ∨ valuation q 1124 = false ∨ valuation q 1136 = true := counterClause1777 (baseVal q)

theorem counterClause1778 (q : Nat → Bool) : valuationOf q 1102 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1137 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1102)) (literal (valuationOf q) (1125)) (literal (valuationOf q) (1137)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 4 3 (meaning1102 q) (meaning1125 q) (meaning1137 q) hs
  change valuationOf q 1102 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1137 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1778 (q : Snake 81) (h : Conditions q) : valuation q 1102 = false ∨ valuation q 1125 = false ∨ valuation q 1137 = true := counterClause1778 (baseVal q)

theorem counterClause1779 (q : Nat → Bool) : valuationOf q 1103 = false ∨ valuationOf q 1135 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1103)) (literal (valuationOf q) (1135)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 5 (meaning1103 q) (meaning1135 q) hs
  change valuationOf q 1103 = false ∨ valuationOf q 1135 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1779 (q : Snake 81) (h : Conditions q) : valuation q 1103 = false ∨ valuation q 1135 = true := counterClause1779 (baseVal q)

theorem counterClause1780 (q : Nat → Bool) : valuationOf q 1103 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1136 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1103)) (literal (valuationOf q) (1123)) (literal (valuationOf q) (1136)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 5 1 (meaning1103 q) (meaning1123 q) (meaning1136 q) hs
  change valuationOf q 1103 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1780 (q : Snake 81) (h : Conditions q) : valuation q 1103 = false ∨ valuation q 1123 = false ∨ valuation q 1136 = true := counterClause1780 (baseVal q)

theorem counterClause1781 (q : Nat → Bool) : valuationOf q 1103 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1137 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1103)) (literal (valuationOf q) (1124)) (literal (valuationOf q) (1137)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 5 2 (meaning1103 q) (meaning1124 q) (meaning1137 q) hs
  change valuationOf q 1103 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1137 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1781 (q : Snake 81) (h : Conditions q) : valuation q 1103 = false ∨ valuation q 1124 = false ∨ valuation q 1137 = true := counterClause1781 (baseVal q)

theorem counterClause1782 (q : Nat → Bool) : valuationOf q 1103 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1138 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1103)) (literal (valuationOf q) (1125)) (literal (valuationOf q) (1138)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 5 3 (meaning1103 q) (meaning1125 q) (meaning1138 q) hs
  change valuationOf q 1103 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1138 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1782 (q : Snake 81) (h : Conditions q) : valuation q 1103 = false ∨ valuation q 1125 = false ∨ valuation q 1138 = true := counterClause1782 (baseVal q)

theorem counterClause1783 (q : Nat → Bool) : valuationOf q 1104 = false ∨ valuationOf q 1136 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1104)) (literal (valuationOf q) (1136)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 6 (meaning1104 q) (meaning1136 q) hs
  change valuationOf q 1104 = false ∨ valuationOf q 1136 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1783 (q : Snake 81) (h : Conditions q) : valuation q 1104 = false ∨ valuation q 1136 = true := counterClause1783 (baseVal q)

theorem counterClause1784 (q : Nat → Bool) : valuationOf q 1104 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1137 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1104)) (literal (valuationOf q) (1123)) (literal (valuationOf q) (1137)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 6 1 (meaning1104 q) (meaning1123 q) (meaning1137 q) hs
  change valuationOf q 1104 = false ∨ valuationOf q 1123 = false ∨ valuationOf q 1137 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1784 (q : Snake 81) (h : Conditions q) : valuation q 1104 = false ∨ valuation q 1123 = false ∨ valuation q 1137 = true := counterClause1784 (baseVal q)

theorem counterClause1785 (q : Nat → Bool) : valuationOf q 1104 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1138 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1104)) (literal (valuationOf q) (1124)) (literal (valuationOf q) (1138)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 6 2 (meaning1104 q) (meaning1124 q) (meaning1138 q) hs
  change valuationOf q 1104 = false ∨ valuationOf q 1124 = false ∨ valuationOf q 1138 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1785 (q : Snake 81) (h : Conditions q) : valuation q 1104 = false ∨ valuation q 1124 = false ∨ valuation q 1138 = true := counterClause1785 (baseVal q)

theorem counterClause1786 (q : Nat → Bool) : valuationOf q 1104 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1139 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1104)) (literal (valuationOf q) (1125)) (literal (valuationOf q) (1139)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 6 3 (meaning1104 q) (meaning1125 q) (meaning1139 q) hs
  change valuationOf q 1104 = false ∨ valuationOf q 1125 = false ∨ valuationOf q 1139 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1786 (q : Snake 81) (h : Conditions q) : valuation q 1104 = false ∨ valuation q 1125 = false ∨ valuation q 1139 = true := counterClause1786 (baseVal q)

theorem counterClause1787 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1137 = false ∨ valuationOf q 1158 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1071)) (literal (valuationOf q) (1137)) (literal (valuationOf q) (1158)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 5 7 (meaning1071 q) (meaning1137 q) (meaning1158 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1137 = false ∨ valuationOf q 1158 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1787 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1137 = false ∨ valuation q 1158 = true := counterClause1787 (baseVal q)

theorem counterClause1788 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1138 = false ∨ valuationOf q 1159 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1071)) (literal (valuationOf q) (1138)) (literal (valuationOf q) (1159)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 5 8 (meaning1071 q) (meaning1138 q) (meaning1159 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1138 = false ∨ valuationOf q 1159 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1788 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1138 = false ∨ valuation q 1159 = true := counterClause1788 (baseVal q)

theorem counterClause1789 (q : Nat → Bool) : valuationOf q 1071 = false ∨ valuationOf q 1139 = false ∨ valuationOf q 1160 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1071)) (literal (valuationOf q) (1139)) (literal (valuationOf q) (1160)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 5 9 (meaning1071 q) (meaning1139 q) (meaning1160 q) hs
  change valuationOf q 1071 = false ∨ valuationOf q 1139 = false ∨ valuationOf q 1160 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1789 (q : Snake 81) (h : Conditions q) : valuation q 1071 = false ∨ valuation q 1139 = false ∨ valuation q 1160 = true := counterClause1789 (baseVal q)

theorem counterClause1790 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1155 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1155)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 6 3 (meaning1072 q) (meaning1133 q) (meaning1155 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1155 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1790 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1133 = false ∨ valuation q 1155 = true := counterClause1790 (baseVal q)

theorem counterClause1791 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1157 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1135)) (literal (valuationOf q) (1157)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 6 5 (meaning1072 q) (meaning1135 q) (meaning1157 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1157 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1791 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1135 = false ∨ valuation q 1157 = true := counterClause1791 (baseVal q)

theorem counterClause1792 (q : Nat → Bool) : valuationOf q 1072 = false ∨ valuationOf q 1136 = false ∨ valuationOf q 1158 = true := by
  have hs : count1147 q = (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) + (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (l₂ := [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1072)) (literal (valuationOf q) (1136)) (literal (valuationOf q) (1158)) (countLit q [-65, -67, -69, -72, -73, -75, -77, -79, -82, -83, -86, -87, -89, -90, -91, -94]) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109, -112, -113, -114, -118, -121, -123, -125, -127]) (count1147 q) 6 6 (meaning1072 q) (meaning1136 q) (meaning1158 q) hs
  change valuationOf q 1072 = false ∨ valuationOf q 1136 = false ∨ valuationOf q 1158 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1792 (q : Snake 81) (h : Conditions q) : valuation q 1072 = false ∨ valuation q 1136 = false ∨ valuation q 1158 = true := counterClause1792 (baseVal q)

theorem block55 (q : Snake 81) (h : Conditions q) : B112E057.Block55 (valuation q) :=
  ⟨clause1761 q h, clause1762 q h, clause1763 q h, clause1764 q h, clause1765 q h, clause1766 q h, clause1767 q h, clause1768 q h, clause1769 q h, clause1770 q h, clause1771 q h, clause1772 q h, clause1773 q h, clause1774 q h, clause1775 q h, clause1776 q h, clause1777 q h, clause1778 q h, clause1779 q h, clause1780 q h, clause1781 q h, clause1782 q h, clause1783 q h, clause1784 q h, clause1785 q h, clause1786 q h, clause1787 q h, clause1788 q h, clause1789 q h, clause1790 q h, clause1791 q h, clause1792 q h⟩

end
end Snake9.Regrowth.E112057
