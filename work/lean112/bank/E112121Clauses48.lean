import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1086 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1099 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1086)) (literal (valuationOf q) (1091)) (literal (valuationOf q) (1099)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 4 1 (meaning1086 q) (meaning1091 q) (meaning1099 q) hs
  change valuationOf q 1086 = false ∨ valuationOf q 1091 = false ∨ valuationOf q 1099 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1086 = false ∨ valuation q 1091 = false ∨ valuation q 1099 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1086 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1100 = true := by
  have hs : count1095 q = (countLit q [-94, -96, -98, -101]) + (countLit q [-103, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-94, -96, -98, -101]) (l₂ := [-103, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1086)) (literal (valuationOf q) (1092)) (literal (valuationOf q) (1100)) (countLit q [-94, -96, -98, -101]) (countLit q [-103, -106, -107, -109]) (count1095 q) 4 2 (meaning1086 q) (meaning1092 q) (meaning1100 q) hs
  change valuationOf q 1086 = false ∨ valuationOf q 1092 = false ∨ valuationOf q 1100 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1086 = false ∨ valuation q 1092 = false ∨ valuation q 1100 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1103 = true := by
  have hs : count1103 q = (countLit q [-110]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1103)) (countLit q [-110]) (countLit q [-112]) (count1103 q) 1 (meaningNeg112 q) (meaning1103 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1103 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1103 = true := by
  have hs : count1103 q = (countLit q [-110]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-110)) (literal (valuationOf q) (1103)) (countLit q [-110]) (countLit q [-112]) (count1103 q) 1 (meaningNeg110 q) (meaning1103 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1103 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1103 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1104 = true := by
  have hs : count1103 q = (countLit q [-110]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-110)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1104)) (countLit q [-110]) (countLit q [-112]) (count1103 q) 1 1 (meaningNeg110 q) (meaningNeg112 q) (meaning1104 q) hs
  change (! (valuationOf q 110)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1104 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 112 = true ∨ valuation q 1104 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1105 = true := by
  have hs : count1105 q = (countLit q [-115]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-118])
  have hm := merge_right (literal (valuationOf q) (-118)) (literal (valuationOf q) (1105)) (countLit q [-115]) (countLit q [-118]) (count1105 q) 1 (meaningNeg118 q) (meaning1105 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1105 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1105 = true := by
  have hs : count1105 q = (countLit q [-115]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-118])
  have hm := merge_left (literal (valuationOf q) (-115)) (literal (valuationOf q) (1105)) (countLit q [-115]) (countLit q [-118]) (count1105 q) 1 (meaningNeg115 q) (meaning1105 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1105 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1105 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 118 = true ∨ valuationOf q 1106 = true := by
  have hs : count1105 q = (countLit q [-115]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-118])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-118)) (literal (valuationOf q) (1106)) (countLit q [-115]) (countLit q [-118]) (count1105 q) 1 1 (meaningNeg115 q) (meaningNeg118 q) (meaning1106 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 118)) = false ∨ valuationOf q 1106 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 118 = true ∨ valuation q 1106 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1105 = false ∨ valuationOf q 1107 = true := by
  have hs : count1107 q = (countLit q [-110, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-115, -118])
  have hm := merge_right (literal (valuationOf q) (1105)) (literal (valuationOf q) (1107)) (countLit q [-110, -112]) (countLit q [-115, -118]) (count1107 q) 1 (meaning1105 q) (meaning1107 q) hs
  change valuationOf q 1105 = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1105 = false ∨ valuation q 1107 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1106 = false ∨ valuationOf q 1108 = true := by
  have hs : count1107 q = (countLit q [-110, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-115, -118])
  have hm := merge_right (literal (valuationOf q) (1106)) (literal (valuationOf q) (1108)) (countLit q [-110, -112]) (countLit q [-115, -118]) (count1107 q) 2 (meaning1106 q) (meaning1108 q) hs
  change valuationOf q 1106 = false ∨ valuationOf q 1108 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1106 = false ∨ valuation q 1108 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1103 = false ∨ valuationOf q 1107 = true := by
  have hs : count1107 q = (countLit q [-110, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-115, -118])
  have hm := merge_left (literal (valuationOf q) (1103)) (literal (valuationOf q) (1107)) (countLit q [-110, -112]) (countLit q [-115, -118]) (count1107 q) 1 (meaning1103 q) (meaning1107 q) hs
  change valuationOf q 1103 = false ∨ valuationOf q 1107 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1103 = false ∨ valuation q 1107 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1103 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1108 = true := by
  have hs : count1107 q = (countLit q [-110, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-115, -118])
  have hm := merge_two (literal (valuationOf q) (1103)) (literal (valuationOf q) (1105)) (literal (valuationOf q) (1108)) (countLit q [-110, -112]) (countLit q [-115, -118]) (count1107 q) 1 1 (meaning1103 q) (meaning1105 q) (meaning1108 q) hs
  change valuationOf q 1103 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1108 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1103 = false ∨ valuation q 1105 = false ∨ valuation q 1108 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1103 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1109 = true := by
  have hs : count1107 q = (countLit q [-110, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-115, -118])
  have hm := merge_two (literal (valuationOf q) (1103)) (literal (valuationOf q) (1106)) (literal (valuationOf q) (1109)) (countLit q [-110, -112]) (countLit q [-115, -118]) (count1107 q) 1 2 (meaning1103 q) (meaning1106 q) (meaning1109 q) hs
  change valuationOf q 1103 = false ∨ valuationOf q 1106 = false ∨ valuationOf q 1109 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1103 = false ∨ valuation q 1106 = false ∨ valuation q 1109 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 1104 = false ∨ valuationOf q 1108 = true := by
  have hs : count1107 q = (countLit q [-110, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-115, -118])
  have hm := merge_left (literal (valuationOf q) (1104)) (literal (valuationOf q) (1108)) (countLit q [-110, -112]) (countLit q [-115, -118]) (count1107 q) 2 (meaning1104 q) (meaning1108 q) hs
  change valuationOf q 1104 = false ∨ valuationOf q 1108 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1104 = false ∨ valuation q 1108 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 1104 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1109 = true := by
  have hs : count1107 q = (countLit q [-110, -112]) + (countLit q [-115, -118]) := List.countP_append (p := literal q) (l₁ := [-110, -112]) (l₂ := [-115, -118])
  have hm := merge_two (literal (valuationOf q) (1104)) (literal (valuationOf q) (1105)) (literal (valuationOf q) (1109)) (countLit q [-110, -112]) (countLit q [-115, -118]) (count1107 q) 2 1 (meaning1104 q) (meaning1105 q) (meaning1109 q) hs
  change valuationOf q 1104 = false ∨ valuationOf q 1105 = false ∨ valuationOf q 1109 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1104 = false ∨ valuation q 1105 = false ∨ valuation q 1109 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 120 = true ∨ valuationOf q 1111 = true := by
  have hs : count1111 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_right (literal (valuationOf q) (-120)) (literal (valuationOf q) (1111)) (countLit q [-119]) (countLit q [-120]) (count1111 q) 1 (meaningNeg120 q) (meaning1111 q) hs
  change (! (valuationOf q 120)) = false ∨ valuationOf q 1111 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 120 = true ∨ valuation q 1111 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 1111 = true := by
  have hs : count1111 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_left (literal (valuationOf q) (-119)) (literal (valuationOf q) (1111)) (countLit q [-119]) (countLit q [-120]) (count1111 q) 1 (meaningNeg119 q) (meaning1111 q) hs
  change (! (valuationOf q 119)) = false ∨ valuationOf q 1111 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 1111 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 119 = true ∨ valuationOf q 120 = true ∨ valuationOf q 1112 = true := by
  have hs : count1111 q = (countLit q [-119]) + (countLit q [-120]) := List.countP_append (p := literal q) (l₁ := [-119]) (l₂ := [-120])
  have hm := merge_two (literal (valuationOf q) (-119)) (literal (valuationOf q) (-120)) (literal (valuationOf q) (1112)) (countLit q [-119]) (countLit q [-120]) (count1111 q) 1 1 (meaningNeg119 q) (meaningNeg120 q) (meaning1112 q) hs
  change (! (valuationOf q 119)) = false ∨ (! (valuationOf q 120)) = false ∨ valuationOf q 1112 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 119 = true ∨ valuation q 120 = true ∨ valuation q 1112 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 126 = true ∨ valuationOf q 1113 = true := by
  have hs : count1113 q = (countLit q [-125]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-126])
  have hm := merge_right (literal (valuationOf q) (-126)) (literal (valuationOf q) (1113)) (countLit q [-125]) (countLit q [-126]) (count1113 q) 1 (meaningNeg126 q) (meaning1113 q) hs
  change (! (valuationOf q 126)) = false ∨ valuationOf q 1113 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 126 = true ∨ valuation q 1113 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 1113 = true := by
  have hs : count1113 q = (countLit q [-125]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-126])
  have hm := merge_left (literal (valuationOf q) (-125)) (literal (valuationOf q) (1113)) (countLit q [-125]) (countLit q [-126]) (count1113 q) 1 (meaningNeg125 q) (meaning1113 q) hs
  change (! (valuationOf q 125)) = false ∨ valuationOf q 1113 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 1113 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 125 = true ∨ valuationOf q 126 = true ∨ valuationOf q 1114 = true := by
  have hs : count1113 q = (countLit q [-125]) + (countLit q [-126]) := List.countP_append (p := literal q) (l₁ := [-125]) (l₂ := [-126])
  have hm := merge_two (literal (valuationOf q) (-125)) (literal (valuationOf q) (-126)) (literal (valuationOf q) (1114)) (countLit q [-125]) (countLit q [-126]) (count1113 q) 1 1 (meaningNeg125 q) (meaningNeg126 q) (meaning1114 q) hs
  change (! (valuationOf q 125)) = false ∨ (! (valuationOf q 126)) = false ∨ valuationOf q 1114 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 125 = true ∨ valuation q 126 = true ∨ valuation q 1114 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 1113 = false ∨ valuationOf q 1115 = true := by
  have hs : count1115 q = (countLit q [-119, -120]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-125, -126])
  have hm := merge_right (literal (valuationOf q) (1113)) (literal (valuationOf q) (1115)) (countLit q [-119, -120]) (countLit q [-125, -126]) (count1115 q) 1 (meaning1113 q) (meaning1115 q) hs
  change valuationOf q 1113 = false ∨ valuationOf q 1115 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 1113 = false ∨ valuation q 1115 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 1114 = false ∨ valuationOf q 1116 = true := by
  have hs : count1115 q = (countLit q [-119, -120]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-125, -126])
  have hm := merge_right (literal (valuationOf q) (1114)) (literal (valuationOf q) (1116)) (countLit q [-119, -120]) (countLit q [-125, -126]) (count1115 q) 2 (meaning1114 q) (meaning1116 q) hs
  change valuationOf q 1114 = false ∨ valuationOf q 1116 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 1114 = false ∨ valuation q 1116 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 1111 = false ∨ valuationOf q 1115 = true := by
  have hs : count1115 q = (countLit q [-119, -120]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-125, -126])
  have hm := merge_left (literal (valuationOf q) (1111)) (literal (valuationOf q) (1115)) (countLit q [-119, -120]) (countLit q [-125, -126]) (count1115 q) 1 (meaning1111 q) (meaning1115 q) hs
  change valuationOf q 1111 = false ∨ valuationOf q 1115 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 1111 = false ∨ valuation q 1115 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 1111 = false ∨ valuationOf q 1113 = false ∨ valuationOf q 1116 = true := by
  have hs : count1115 q = (countLit q [-119, -120]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-125, -126])
  have hm := merge_two (literal (valuationOf q) (1111)) (literal (valuationOf q) (1113)) (literal (valuationOf q) (1116)) (countLit q [-119, -120]) (countLit q [-125, -126]) (count1115 q) 1 1 (meaning1111 q) (meaning1113 q) (meaning1116 q) hs
  change valuationOf q 1111 = false ∨ valuationOf q 1113 = false ∨ valuationOf q 1116 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 1111 = false ∨ valuation q 1113 = false ∨ valuation q 1116 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 1111 = false ∨ valuationOf q 1114 = false ∨ valuationOf q 1117 = true := by
  have hs : count1115 q = (countLit q [-119, -120]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-125, -126])
  have hm := merge_two (literal (valuationOf q) (1111)) (literal (valuationOf q) (1114)) (literal (valuationOf q) (1117)) (countLit q [-119, -120]) (countLit q [-125, -126]) (count1115 q) 1 2 (meaning1111 q) (meaning1114 q) (meaning1117 q) hs
  change valuationOf q 1111 = false ∨ valuationOf q 1114 = false ∨ valuationOf q 1117 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 1111 = false ∨ valuation q 1114 = false ∨ valuation q 1117 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 1112 = false ∨ valuationOf q 1116 = true := by
  have hs : count1115 q = (countLit q [-119, -120]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-125, -126])
  have hm := merge_left (literal (valuationOf q) (1112)) (literal (valuationOf q) (1116)) (countLit q [-119, -120]) (countLit q [-125, -126]) (count1115 q) 2 (meaning1112 q) (meaning1116 q) hs
  change valuationOf q 1112 = false ∨ valuationOf q 1116 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 1112 = false ∨ valuation q 1116 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 1112 = false ∨ valuationOf q 1113 = false ∨ valuationOf q 1117 = true := by
  have hs : count1115 q = (countLit q [-119, -120]) + (countLit q [-125, -126]) := List.countP_append (p := literal q) (l₁ := [-119, -120]) (l₂ := [-125, -126])
  have hm := merge_two (literal (valuationOf q) (1112)) (literal (valuationOf q) (1113)) (literal (valuationOf q) (1117)) (countLit q [-119, -120]) (countLit q [-125, -126]) (count1115 q) 2 1 (meaning1112 q) (meaning1113 q) (meaning1117 q) hs
  change valuationOf q 1112 = false ∨ valuationOf q 1113 = false ∨ valuationOf q 1117 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 1112 = false ∨ valuation q 1113 = false ∨ valuation q 1117 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 1115 = false ∨ valuationOf q 1119 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1115)) (literal (valuationOf q) (1119)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 1 (meaning1115 q) (meaning1119 q) hs
  change valuationOf q 1115 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 1115 = false ∨ valuation q 1119 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 1116 = false ∨ valuationOf q 1120 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1116)) (literal (valuationOf q) (1120)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 2 (meaning1116 q) (meaning1120 q) hs
  change valuationOf q 1116 = false ∨ valuationOf q 1120 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 1116 = false ∨ valuation q 1120 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1117 = false ∨ valuationOf q 1121 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_right (literal (valuationOf q) (1117)) (literal (valuationOf q) (1121)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 3 (meaning1117 q) (meaning1121 q) hs
  change valuationOf q 1117 = false ∨ valuationOf q 1121 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1117 = false ∨ valuation q 1121 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1107 = false ∨ valuationOf q 1119 = true := by
  have hs : count1119 q = (countLit q [-110, -112, -115, -118]) + (countLit q [-119, -120, -125, -126]) := List.countP_append (p := literal q) (l₁ := [-110, -112, -115, -118]) (l₂ := [-119, -120, -125, -126])
  have hm := merge_left (literal (valuationOf q) (1107)) (literal (valuationOf q) (1119)) (countLit q [-110, -112, -115, -118]) (countLit q [-119, -120, -125, -126]) (count1119 q) 1 (meaning1107 q) (meaning1119 q) hs
  change valuationOf q 1107 = false ∨ valuationOf q 1119 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1107 = false ∨ valuation q 1119 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E121.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112121
