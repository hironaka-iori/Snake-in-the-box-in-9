import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 1107 = false ∨ valuationOf q 1115 = false ∨ valuationOf q 1120 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1107)) (literal (valuationOf q) (1115)) (literal (valuationOf q) (1120)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 1 1 (meaning1107 q) (meaning1115 q) (meaning1120 q) hs
  change valuationOf q 1107 = false ∨ valuationOf q 1115 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 1107 = false ∨ valuation q 1115 = false ∨ valuation q 1120 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 1107 = false ∨ valuationOf q 1116 = false ∨ valuationOf q 1121 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1107)) (literal (valuationOf q) (1116)) (literal (valuationOf q) (1121)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 1 2 (meaning1107 q) (meaning1116 q) (meaning1121 q) hs
  change valuationOf q 1107 = false ∨ valuationOf q 1116 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 1107 = false ∨ valuation q 1116 = false ∨ valuation q 1121 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 1108 = false ∨ valuationOf q 1120 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1108)) (literal (valuationOf q) (1120)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 2 (meaning1108 q) (meaning1120 q) hs
  change valuationOf q 1108 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 1108 = false ∨ valuation q 1120 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 1108 = false ∨ valuationOf q 1115 = false ∨ valuationOf q 1121 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1108)) (literal (valuationOf q) (1115)) (literal (valuationOf q) (1121)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 2 1 (meaning1108 q) (meaning1115 q) (meaning1121 q) hs
  change valuationOf q 1108 = false ∨ valuationOf q 1115 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 1108 = false ∨ valuation q 1115 = false ∨ valuation q 1121 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 1108 = false ∨ valuationOf q 1116 = false ∨ valuationOf q 1122 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1108)) (literal (valuationOf q) (1116)) (literal (valuationOf q) (1122)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 2 2 (meaning1108 q) (meaning1116 q) (meaning1122 q) hs
  change valuationOf q 1108 = false ∨ valuationOf q 1116 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 1108 = false ∨ valuation q 1116 = false ∨ valuation q 1122 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 1109 = false ∨ valuationOf q 1121 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1109)) (literal (valuationOf q) (1121)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 3 (meaning1109 q) (meaning1121 q) hs
  change valuationOf q 1109 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 1109 = false ∨ valuation q 1121 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1109 = false ∨ valuationOf q 1115 = false ∨ valuationOf q 1122 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1109)) (literal (valuationOf q) (1115)) (literal (valuationOf q) (1122)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 3 1 (meaning1109 q) (meaning1115 q) (meaning1122 q) hs
  change valuationOf q 1109 = false ∨ valuationOf q 1115 = false ∨ valuationOf q 1122 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1109 = false ∨ valuation q 1115 = false ∨ valuation q 1122 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1095 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1129 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1095)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1129)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 1 2 (meaning1095 q) (meaning1120 q) (meaning1129 q) hs
  change valuationOf q 1095 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1129 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1095 = false ∨ valuation q 1120 = false ∨ valuation q 1129 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1095 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1130 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1095)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1130)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 1 3 (meaning1095 q) (meaning1121 q) (meaning1130 q) hs
  change valuationOf q 1095 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1130 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1095 = false ∨ valuation q 1121 = false ∨ valuation q 1130 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1096 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1129 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1096)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1129)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 2 1 (meaning1096 q) (meaning1119 q) (meaning1129 q) hs
  change valuationOf q 1096 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1129 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1096 = false ∨ valuation q 1119 = false ∨ valuation q 1129 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 1096 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1130 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1096)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1130)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 2 2 (meaning1096 q) (meaning1120 q) (meaning1130 q) hs
  change valuationOf q 1096 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1130 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 1096 = false ∨ valuation q 1120 = false ∨ valuation q 1130 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 1096 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1131 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1096)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1131)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 2 3 (meaning1096 q) (meaning1121 q) (meaning1131 q) hs
  change valuationOf q 1096 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1131 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 1096 = false ∨ valuation q 1121 = false ∨ valuation q 1131 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 1096 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1132 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1096)) (literal (valuationOf q) (1122)) (literal (valuationOf q) (1132)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 2 4 (meaning1096 q) (meaning1122 q) (meaning1132 q) hs
  change valuationOf q 1096 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1132 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 1096 = false ∨ valuation q 1122 = false ∨ valuation q 1132 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 1097 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1130 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1097)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1130)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 3 1 (meaning1097 q) (meaning1119 q) (meaning1130 q) hs
  change valuationOf q 1097 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1130 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 1097 = false ∨ valuation q 1119 = false ∨ valuation q 1130 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 1097 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1131 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1097)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1131)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 3 2 (meaning1097 q) (meaning1120 q) (meaning1131 q) hs
  change valuationOf q 1097 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1131 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 1097 = false ∨ valuation q 1120 = false ∨ valuation q 1131 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 1097 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1132 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1097)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1132)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 3 3 (meaning1097 q) (meaning1121 q) (meaning1132 q) hs
  change valuationOf q 1097 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1132 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 1097 = false ∨ valuation q 1121 = false ∨ valuation q 1132 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 1097 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1133 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1097)) (literal (valuationOf q) (1122)) (literal (valuationOf q) (1133)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 3 4 (meaning1097 q) (meaning1122 q) (meaning1133 q) hs
  change valuationOf q 1097 = false ∨ valuationOf q 1122 = false ∨ valuationOf q 1133 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 1097 = false ∨ valuation q 1122 = false ∨ valuation q 1133 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 1098 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1131 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1098)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1131)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 4 1 (meaning1098 q) (meaning1119 q) (meaning1131 q) hs
  change valuationOf q 1098 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1131 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 1098 = false ∨ valuation q 1119 = false ∨ valuation q 1131 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 1098 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1132 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1098)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1132)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 4 2 (meaning1098 q) (meaning1120 q) (meaning1132 q) hs
  change valuationOf q 1098 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1132 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 1098 = false ∨ valuation q 1120 = false ∨ valuation q 1132 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 1098 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1133 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1098)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1133)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 4 3 (meaning1098 q) (meaning1121 q) (meaning1133 q) hs
  change valuationOf q 1098 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1133 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 1098 = false ∨ valuation q 1121 = false ∨ valuation q 1133 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 1099 = false ∨ valuationOf q 1131 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1099)) (literal (valuationOf q) (1131)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 5 (meaning1099 q) (meaning1131 q) hs
  change valuationOf q 1099 = false ∨ valuationOf q 1131 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 1099 = false ∨ valuation q 1131 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1099 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1132 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1099)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1132)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 5 1 (meaning1099 q) (meaning1119 q) (meaning1132 q) hs
  change valuationOf q 1099 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1132 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1099 = false ∨ valuation q 1119 = false ∨ valuation q 1132 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1099 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1133 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1099)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1133)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 5 2 (meaning1099 q) (meaning1120 q) (meaning1133 q) hs
  change valuationOf q 1099 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1133 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1099 = false ∨ valuation q 1120 = false ∨ valuation q 1133 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 1099 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1134 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1099)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1134)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 5 3 (meaning1099 q) (meaning1121 q) (meaning1134 q) hs
  change valuationOf q 1099 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1134 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 1099 = false ∨ valuation q 1121 = false ∨ valuation q 1134 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 1100 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1133 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1100)) (literal (valuationOf q) (1119)) (literal (valuationOf q) (1133)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 6 1 (meaning1100 q) (meaning1119 q) (meaning1133 q) hs
  change valuationOf q 1100 = false ∨ valuationOf q 1119 = false ∨ valuationOf q 1133 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 1100 = false ∨ valuation q 1119 = false ∨ valuation q 1133 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 1100 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1134 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1100)) (literal (valuationOf q) (1120)) (literal (valuationOf q) (1134)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 6 2 (meaning1100 q) (meaning1120 q) (meaning1134 q) hs
  change valuationOf q 1100 = false ∨ valuationOf q 1120 = false ∨ valuationOf q 1134 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 1100 = false ∨ valuation q 1120 = false ∨ valuation q 1134 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 1100 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1135 = true := by
  have hs : count1127 q = (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) + (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101, -103, -106, -107, -109]) (l₂ := [-110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1100)) (literal (valuationOf q) (1121)) (literal (valuationOf q) (1135)) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109]) (countLit q [-110, -112, -115, -118, -119, -120, -125, -126]) (count1127 q) 6 3 (meaning1100 q) (meaning1121 q) (meaning1135 q) hs
  change valuationOf q 1100 = false ∨ valuationOf q 1121 = false ∨ valuationOf q 1135 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 1100 = false ∨ valuation q 1121 = false ∨ valuation q 1135 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 1063 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1152 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1063)) (literal (valuationOf q) (1135)) (literal (valuationOf q) (1152)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 1 9 (meaning1063 q) (meaning1135 q) (meaning1152 q) hs
  change valuationOf q 1063 = false ∨ valuationOf q 1135 = false ∨ valuationOf q 1152 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 1063 = false ∨ valuation q 1135 = false ∨ valuation q 1152 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1148 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1130)) (literal (valuationOf q) (1148)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 2 4 (meaning1064 q) (meaning1130 q) (meaning1148 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1130 = false ∨ valuationOf q 1148 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1130 = false ∨ valuation q 1148 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1149 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1131)) (literal (valuationOf q) (1149)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 2 5 (meaning1064 q) (meaning1131 q) (meaning1149 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1131 = false ∨ valuationOf q 1149 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1131 = false ∨ valuation q 1149 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1150 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1132)) (literal (valuationOf q) (1150)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 2 6 (meaning1064 q) (meaning1132 q) (meaning1150 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1132 = false ∨ valuationOf q 1150 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1132 = false ∨ valuation q 1150 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 1064 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1151 = true := by
  have hs : count1143 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) + (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (l₂ := [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126])
  have hm := merge_two (literal (valuationOf q) (1064)) (literal (valuationOf q) (1133)) (literal (valuationOf q) (1151)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78, -79, -81, -85, -86, -88, -89, -90, -93]) (countLit q [-94, -96, -98, -101, -103, -106, -107, -109, -110, -112, -115, -118, -119, -120, -125, -126]) (count1143 q) 2 7 (meaning1064 q) (meaning1133 q) (meaning1151 q) hs
  change valuationOf q 1064 = false ∨ valuationOf q 1133 = false ∨ valuationOf q 1151 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 1064 = false ∨ valuation q 1133 = false ∨ valuation q 1151 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E121.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112121
