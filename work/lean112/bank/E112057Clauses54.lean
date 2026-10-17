import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec54 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1729 (q : Nat → Bool) : valuationOf q 1109 = false ∨ valuationOf q 1111 = true := by
  have hs : count1111 q = (countLit q [-112, -113]) + (countLit q [-114, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -118])
  have hm := merge_right (literal (valuationOf q) (1109)) (literal (valuationOf q) (1111)) (countLit q [-112, -113]) (countLit q [-114, -118]) (count1111 q) 1 (meaning1109 q) (meaning1111 q) hs
  change valuationOf q 1109 = false ∨ valuationOf q 1111 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1729 (q : Snake 81) (h : Conditions q) : valuation q 1109 = false ∨ valuation q 1111 = true := counterClause1729 (baseVal q)

theorem counterClause1730 (q : Nat → Bool) : valuationOf q 1110 = false ∨ valuationOf q 1112 = true := by
  have hs : count1111 q = (countLit q [-112, -113]) + (countLit q [-114, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -118])
  have hm := merge_right (literal (valuationOf q) (1110)) (literal (valuationOf q) (1112)) (countLit q [-112, -113]) (countLit q [-114, -118]) (count1111 q) 2 (meaning1110 q) (meaning1112 q) hs
  change valuationOf q 1110 = false ∨ valuationOf q 1112 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1730 (q : Snake 81) (h : Conditions q) : valuation q 1110 = false ∨ valuation q 1112 = true := counterClause1730 (baseVal q)

theorem counterClause1731 (q : Nat → Bool) : valuationOf q 1107 = false ∨ valuationOf q 1111 = true := by
  have hs : count1111 q = (countLit q [-112, -113]) + (countLit q [-114, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -118])
  have hm := merge_left (literal (valuationOf q) (1107)) (literal (valuationOf q) (1111)) (countLit q [-112, -113]) (countLit q [-114, -118]) (count1111 q) 1 (meaning1107 q) (meaning1111 q) hs
  change valuationOf q 1107 = false ∨ valuationOf q 1111 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1731 (q : Snake 81) (h : Conditions q) : valuation q 1107 = false ∨ valuation q 1111 = true := counterClause1731 (baseVal q)

theorem counterClause1732 (q : Nat → Bool) : valuationOf q 1107 = false ∨ valuationOf q 1109 = false ∨ valuationOf q 1112 = true := by
  have hs : count1111 q = (countLit q [-112, -113]) + (countLit q [-114, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -118])
  have hm := merge_two (literal (valuationOf q) (1107)) (literal (valuationOf q) (1109)) (literal (valuationOf q) (1112)) (countLit q [-112, -113]) (countLit q [-114, -118]) (count1111 q) 1 1 (meaning1107 q) (meaning1109 q) (meaning1112 q) hs
  change valuationOf q 1107 = false ∨ valuationOf q 1109 = false ∨ valuationOf q 1112 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1732 (q : Snake 81) (h : Conditions q) : valuation q 1107 = false ∨ valuation q 1109 = false ∨ valuation q 1112 = true := counterClause1732 (baseVal q)

theorem counterClause1733 (q : Nat → Bool) : valuationOf q 1107 = false ∨ valuationOf q 1110 = false ∨ valuationOf q 1113 = true := by
  have hs : count1111 q = (countLit q [-112, -113]) + (countLit q [-114, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -118])
  have hm := merge_two (literal (valuationOf q) (1107)) (literal (valuationOf q) (1110)) (literal (valuationOf q) (1113)) (countLit q [-112, -113]) (countLit q [-114, -118]) (count1111 q) 1 2 (meaning1107 q) (meaning1110 q) (meaning1113 q) hs
  change valuationOf q 1107 = false ∨ valuationOf q 1110 = false ∨ valuationOf q 1113 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1733 (q : Snake 81) (h : Conditions q) : valuation q 1107 = false ∨ valuation q 1110 = false ∨ valuation q 1113 = true := counterClause1733 (baseVal q)

theorem counterClause1734 (q : Nat → Bool) : valuationOf q 1108 = false ∨ valuationOf q 1112 = true := by
  have hs : count1111 q = (countLit q [-112, -113]) + (countLit q [-114, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -118])
  have hm := merge_left (literal (valuationOf q) (1108)) (literal (valuationOf q) (1112)) (countLit q [-112, -113]) (countLit q [-114, -118]) (count1111 q) 2 (meaning1108 q) (meaning1112 q) hs
  change valuationOf q 1108 = false ∨ valuationOf q 1112 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1734 (q : Snake 81) (h : Conditions q) : valuation q 1108 = false ∨ valuation q 1112 = true := counterClause1734 (baseVal q)

theorem counterClause1735 (q : Nat → Bool) : valuationOf q 1108 = false ∨ valuationOf q 1109 = false ∨ valuationOf q 1113 = true := by
  have hs : count1111 q = (countLit q [-112, -113]) + (countLit q [-114, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -118])
  have hm := merge_two (literal (valuationOf q) (1108)) (literal (valuationOf q) (1109)) (literal (valuationOf q) (1113)) (countLit q [-112, -113]) (countLit q [-114, -118]) (count1111 q) 2 1 (meaning1108 q) (meaning1109 q) (meaning1113 q) hs
  change valuationOf q 1108 = false ∨ valuationOf q 1109 = false ∨ valuationOf q 1113 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1735 (q : Snake 81) (h : Conditions q) : valuation q 1108 = false ∨ valuation q 1109 = false ∨ valuation q 1113 = true := counterClause1735 (baseVal q)

theorem counterClause1736 (q : Nat → Bool) : valuationOf q 1108 = false ∨ valuationOf q 1110 = false ∨ valuationOf q 1114 = true := by
  have hs : count1111 q = (countLit q [-112, -113]) + (countLit q [-114, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -113]) (l₂ := [-114, -118])
  have hm := merge_two (literal (valuationOf q) (1108)) (literal (valuationOf q) (1110)) (literal (valuationOf q) (1114)) (countLit q [-112, -113]) (countLit q [-114, -118]) (count1111 q) 2 2 (meaning1108 q) (meaning1110 q) (meaning1114 q) hs
  change valuationOf q 1108 = false ∨ valuationOf q 1110 = false ∨ valuationOf q 1114 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1736 (q : Snake 81) (h : Conditions q) : valuation q 1108 = false ∨ valuation q 1110 = false ∨ valuation q 1114 = true := counterClause1736 (baseVal q)

theorem counterClause1737 (q : Nat → Bool) : valuationOf q 123 = true ∨ valuationOf q 1115 = true := by
  have hs : count1115 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_right (literal (valuationOf q) (-123)) (literal (valuationOf q) (1115)) (countLit q [-121]) (countLit q [-123]) (count1115 q) 1 (meaningNeg123 q) (meaning1115 q) hs
  change (! (valuationOf q 123)) = false ∨ valuationOf q 1115 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1737 (q : Snake 81) (h : Conditions q) : valuation q 123 = true ∨ valuation q 1115 = true := counterClause1737 (baseVal q)

theorem counterClause1738 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 1115 = true := by
  have hs : count1115 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_left (literal (valuationOf q) (-121)) (literal (valuationOf q) (1115)) (countLit q [-121]) (countLit q [-123]) (count1115 q) 1 (meaningNeg121 q) (meaning1115 q) hs
  change (! (valuationOf q 121)) = false ∨ valuationOf q 1115 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1738 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 1115 = true := counterClause1738 (baseVal q)

theorem counterClause1739 (q : Nat → Bool) : valuationOf q 121 = true ∨ valuationOf q 123 = true ∨ valuationOf q 1116 = true := by
  have hs : count1115 q = (countLit q [-121]) + (countLit q [-123]) := List.countP_append (p := literal q) (l₁ := [-121]) (l₂ := [-123])
  have hm := merge_two (literal (valuationOf q) (-121)) (literal (valuationOf q) (-123)) (literal (valuationOf q) (1116)) (countLit q [-121]) (countLit q [-123]) (count1115 q) 1 1 (meaningNeg121 q) (meaningNeg123 q) (meaning1116 q) hs
  change (! (valuationOf q 121)) = false ∨ (! (valuationOf q 123)) = false ∨ valuationOf q 1116 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1739 (q : Snake 81) (h : Conditions q) : valuation q 121 = true ∨ valuation q 123 = true ∨ valuation q 1116 = true := counterClause1739 (baseVal q)

theorem counterClause1740 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 1117 = true := by
  have hs : count1117 q = (countLit q [-125]) + (countLit q [-127]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-127])
  have hm := merge_left (literal (valuationOf q) (-125)) (literal (valuationOf q) (1117)) (countLit q [-125]) (countLit q [-127]) (count1117 q) 1 (meaningNeg125 q) (meaning1117 q) hs
  change (! (valuationOf q 125)) = false ∨ valuationOf q 1117 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1740 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 1117 = true := counterClause1740 (baseVal q)

theorem counterClause1741 (q : Nat → Bool) : valuationOf q 1117 = false ∨ valuationOf q 1119 = true := by
  have hs : count1119 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_right (literal (valuationOf q) (1117)) (literal (valuationOf q) (1119)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1119 q) 1 (meaning1117 q) (meaning1119 q) hs
  change valuationOf q 1117 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1741 (q : Snake 81) (h : Conditions q) : valuation q 1117 = false ∨ valuation q 1119 = true := counterClause1741 (baseVal q)

theorem counterClause1742 (q : Nat → Bool) : valuationOf q 1115 = false ∨ valuationOf q 1119 = true := by
  have hs : count1119 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_left (literal (valuationOf q) (1115)) (literal (valuationOf q) (1119)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1119 q) 1 (meaning1115 q) (meaning1119 q) hs
  change valuationOf q 1115 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1742 (q : Snake 81) (h : Conditions q) : valuation q 1115 = false ∨ valuation q 1119 = true := counterClause1742 (baseVal q)

theorem counterClause1743 (q : Nat → Bool) : valuationOf q 1115 = false ∨ valuationOf q 1117 = false ∨ valuationOf q 1120 = true := by
  have hs : count1119 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_two (literal (valuationOf q) (1115)) (literal (valuationOf q) (1117)) (literal (valuationOf q) (1120)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1119 q) 1 1 (meaning1115 q) (meaning1117 q) (meaning1120 q) hs
  change valuationOf q 1115 = false ∨ valuationOf q 1117 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1743 (q : Snake 81) (h : Conditions q) : valuation q 1115 = false ∨ valuation q 1117 = false ∨ valuation q 1120 = true := counterClause1743 (baseVal q)

theorem counterClause1744 (q : Nat → Bool) : valuationOf q 1116 = false ∨ valuationOf q 1120 = true := by
  have hs : count1119 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_left (literal (valuationOf q) (1116)) (literal (valuationOf q) (1120)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1119 q) 2 (meaning1116 q) (meaning1120 q) hs
  change valuationOf q 1116 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1744 (q : Snake 81) (h : Conditions q) : valuation q 1116 = false ∨ valuation q 1120 = true := counterClause1744 (baseVal q)

theorem counterClause1745 (q : Nat → Bool) : valuationOf q 1116 = false ∨ valuationOf q 1117 = false ∨ valuationOf q 1121 = true := by
  have hs : count1119 q = (countLit q [-121, -123]) + (countLit q [-125, -127]) := List.countP_append (p := literal q) (l₁ := [-121, -123]) (l₂ := [-125, -127])
  have hm := merge_two (literal (valuationOf q) (1116)) (literal (valuationOf q) (1117)) (literal (valuationOf q) (1121)) (countLit q [-121, -123]) (countLit q [-125, -127]) (count1119 q) 2 1 (meaning1116 q) (meaning1117 q) (meaning1121 q) hs
  change valuationOf q 1116 = false ∨ valuationOf q 1117 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1745 (q : Snake 81) (h : Conditions q) : valuation q 1116 = false ∨ valuation q 1117 = false ∨ valuation q 1121 = true := counterClause1745 (baseVal q)

theorem counterClause1746 (q : Nat → Bool) : valuationOf q 1119 = false ∨ valuationOf q 1123 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1119)) (literal (valuationOf q) (1123)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 1 (meaning1119 q) (meaning1123 q) hs
  change valuationOf q 1119 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1746 (q : Snake 81) (h : Conditions q) : valuation q 1119 = false ∨ valuation q 1123 = true := counterClause1746 (baseVal q)

theorem counterClause1747 (q : Nat → Bool) : valuationOf q 1120 = false ∨ valuationOf q 1124 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1120)) (literal (valuationOf q) (1124)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 2 (meaning1120 q) (meaning1124 q) hs
  change valuationOf q 1120 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1747 (q : Snake 81) (h : Conditions q) : valuation q 1120 = false ∨ valuation q 1124 = true := counterClause1747 (baseVal q)

theorem counterClause1748 (q : Nat → Bool) : valuationOf q 1121 = false ∨ valuationOf q 1125 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1121)) (literal (valuationOf q) (1125)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 3 (meaning1121 q) (meaning1125 q) hs
  change valuationOf q 1121 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1748 (q : Snake 81) (h : Conditions q) : valuation q 1121 = false ∨ valuation q 1125 = true := counterClause1748 (baseVal q)

theorem counterClause1749 (q : Nat → Bool) : valuationOf q 1111 = false ∨ valuationOf q 1123 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1111)) (literal (valuationOf q) (1123)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 1 (meaning1111 q) (meaning1123 q) hs
  change valuationOf q 1111 = false ∨ valuationOf q 1123 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1749 (q : Snake 81) (h : Conditions q) : valuation q 1111 = false ∨ valuation q 1123 = true := counterClause1749 (baseVal q)

theorem counterClause1750 (q : Nat → Bool) : valuationOf q 1111 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1124 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1111)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1124)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 1 1 (meaning1111 q) (meaning1119 q) (meaning1124 q) hs
  change valuationOf q 1111 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1750 (q : Snake 81) (h : Conditions q) : valuation q 1111 = false ∨ valuation q 1119 = false ∨ valuation q 1124 = true := counterClause1750 (baseVal q)

theorem counterClause1751 (q : Nat → Bool) : valuationOf q 1111 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1125 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1111)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1125)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 1 2 (meaning1111 q) (meaning1120 q) (meaning1125 q) hs
  change valuationOf q 1111 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1751 (q : Snake 81) (h : Conditions q) : valuation q 1111 = false ∨ valuation q 1120 = false ∨ valuation q 1125 = true := counterClause1751 (baseVal q)

theorem counterClause1752 (q : Nat → Bool) : valuationOf q 1111 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1126 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1111)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1126)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 1 3 (meaning1111 q) (meaning1121 q) (meaning1126 q) hs
  change valuationOf q 1111 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1126 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1752 (q : Snake 81) (h : Conditions q) : valuation q 1111 = false ∨ valuation q 1121 = false ∨ valuation q 1126 = true := counterClause1752 (baseVal q)

theorem counterClause1753 (q : Nat → Bool) : valuationOf q 1112 = false ∨ valuationOf q 1124 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1112)) (literal (valuationOf q) (1124)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 2 (meaning1112 q) (meaning1124 q) hs
  change valuationOf q 1112 = false ∨ valuationOf q 1124 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1753 (q : Snake 81) (h : Conditions q) : valuation q 1112 = false ∨ valuation q 1124 = true := counterClause1753 (baseVal q)

theorem counterClause1754 (q : Nat → Bool) : valuationOf q 1112 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1125 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1112)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1125)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 2 1 (meaning1112 q) (meaning1119 q) (meaning1125 q) hs
  change valuationOf q 1112 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1754 (q : Snake 81) (h : Conditions q) : valuation q 1112 = false ∨ valuation q 1119 = false ∨ valuation q 1125 = true := counterClause1754 (baseVal q)

theorem counterClause1755 (q : Nat → Bool) : valuationOf q 1112 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1126 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1112)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1126)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 2 2 (meaning1112 q) (meaning1120 q) (meaning1126 q) hs
  change valuationOf q 1112 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1126 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1755 (q : Snake 81) (h : Conditions q) : valuation q 1112 = false ∨ valuation q 1120 = false ∨ valuation q 1126 = true := counterClause1755 (baseVal q)

theorem counterClause1756 (q : Nat → Bool) : valuationOf q 1113 = false ∨ valuationOf q 1125 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1113)) (literal (valuationOf q) (1125)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 3 (meaning1113 q) (meaning1125 q) hs
  change valuationOf q 1113 = false ∨ valuationOf q 1125 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1756 (q : Snake 81) (h : Conditions q) : valuation q 1113 = false ∨ valuation q 1125 = true := counterClause1756 (baseVal q)

theorem counterClause1757 (q : Nat → Bool) : valuationOf q 1113 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1126 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_two (literal (valuationOf q) (1113)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1126)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 3 1 (meaning1113 q) (meaning1119 q) (meaning1126 q) hs
  change valuationOf q 1113 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1126 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1757 (q : Snake 81) (h : Conditions q) : valuation q 1113 = false ∨ valuation q 1119 = false ∨ valuation q 1126 = true := counterClause1757 (baseVal q)

theorem counterClause1758 (q : Nat → Bool) : valuationOf q 1114 = false ∨ valuationOf q 1126 = true := by
  have hs : count1123 q = (countLit q [-112, -113, -114, -118]) + (countLit q [-121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-112, -113, -114, -118]) (l₂ := [-121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1114)) (literal (valuationOf q) (1126)) (countLit q [-112, -113, -114, -118]) (countLit q [-121, -123, -125, -127]) (count1123 q) 4 (meaning1114 q) (meaning1126 q) hs
  change valuationOf q 1114 = false ∨ valuationOf q 1126 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1758 (q : Snake 81) (h : Conditions q) : valuation q 1114 = false ∨ valuation q 1126 = true := counterClause1758 (baseVal q)

theorem counterClause1759 (q : Nat → Bool) : valuationOf q 1124 = false ∨ valuationOf q 1132 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_right (literal (valuationOf q) (1124)) (literal (valuationOf q) (1132)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 2 (meaning1124 q) (meaning1132 q) hs
  change valuationOf q 1124 = false ∨ valuationOf q 1132 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1759 (q : Snake 81) (h : Conditions q) : valuation q 1124 = false ∨ valuation q 1132 = true := counterClause1759 (baseVal q)

theorem counterClause1760 (q : Nat → Bool) : valuationOf q 1099 = false ∨ valuationOf q 1131 = true := by
  have hs : count1131 q = (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) + (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) := List.countP_append (p := literal q) (l₁ := [-95, -96, -97, -101, -103, -105, -107, -109]) (l₂ := [-112, -113, -114, -118, -121, -123, -125, -127])
  have hm := merge_left (literal (valuationOf q) (1099)) (literal (valuationOf q) (1131)) (countLit q [-95, -96, -97, -101, -103, -105, -107, -109]) (countLit q [-112, -113, -114, -118, -121, -123, -125, -127]) (count1131 q) 1 (meaning1099 q) (meaning1131 q) hs
  change valuationOf q 1099 = false ∨ valuationOf q 1131 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1760 (q : Snake 81) (h : Conditions q) : valuation q 1099 = false ∨ valuation q 1131 = true := counterClause1760 (baseVal q)

theorem block54 (q : Snake 81) (h : Conditions q) : B112E057.Block54 (valuation q) :=
  ⟨clause1729 q h, clause1730 q h, clause1731 q h, clause1732 q h, clause1733 q h, clause1734 q h, clause1735 q h, clause1736 q h, clause1737 q h, clause1738 q h, clause1739 q h, clause1740 q h, clause1741 q h, clause1742 q h, clause1743 q h, clause1744 q h, clause1745 q h, clause1746 q h, clause1747 q h, clause1748 q h, clause1749 q h, clause1750 q h, clause1751 q h, clause1752 q h, clause1753 q h, clause1754 q h, clause1755 q h, clause1756 q h, clause1757 q h, clause1758 q h, clause1759 q h, clause1760 q h⟩

end
end Snake9.Regrowth.E112057
