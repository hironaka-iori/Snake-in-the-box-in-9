import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1610 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1610)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 5 1 (meaning1541 q) (meaning1591 q) (meaning1610 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1591 = false ∨ valuation q 1610 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1611 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1611)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 5 2 (meaning1541 q) (meaning1592 q) (meaning1611 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1592 = false ∨ valuation q 1611 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1612 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1612)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 5 3 (meaning1541 q) (meaning1593 q) (meaning1612 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1593 = false ∨ valuation q 1612 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1613 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1613)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 5 4 (meaning1541 q) (meaning1594 q) (meaning1613 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1594 = false ∨ valuation q 1613 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1612 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1612)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 6 2 (meaning1542 q) (meaning1592 q) (meaning1612 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1592 = false ∨ valuation q 1612 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1613 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1613)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 6 3 (meaning1542 q) (meaning1593 q) (meaning1613 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1593 = false ∨ valuation q 1613 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1614 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1614)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 6 4 (meaning1542 q) (meaning1594 q) (meaning1614 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1594 = false ∨ valuation q 1614 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1613 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1613)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 7 2 (meaning1543 q) (meaning1592 q) (meaning1613 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1592 = false ∨ valuation q 1613 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1614 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1614)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 7 3 (meaning1543 q) (meaning1593 q) (meaning1614 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1593 = false ∨ valuation q 1614 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1615 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1543)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1615)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 7 4 (meaning1543 q) (meaning1594 q) (meaning1615 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1594 = false ∨ valuation q 1615 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1614 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1544)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1614)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 8 2 (meaning1544 q) (meaning1592 q) (meaning1614 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1592 = false ∨ valuation q 1614 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1615 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1545)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1615)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 9 2 (meaning1545 q) (meaning1592 q) (meaning1615 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1592 = false ∨ valuation q 1615 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1636 = true := by
  have hs : count1621 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) + (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (l₂ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1621 q) 5 11 (meaning1485 q) (meaning1615 q) (meaning1636 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1615 = false ∨ valuation q 1636 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1636 = true := by
  have hs : count1621 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) + (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (l₂ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1614)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1621 q) 6 10 (meaning1486 q) (meaning1614 q) (meaning1636 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1614 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1614 = false ∨ valuation q 1636 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1636 = true := by
  have hs : count1621 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) + (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (l₂ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1621 q) 7 9 (meaning1487 q) (meaning1613 q) (meaning1636 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1613 = false ∨ valuation q 1636 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1636 = true := by
  have hs : count1621 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) + (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (l₂ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1621 q) 8 8 (meaning1488 q) (meaning1612 q) (meaning1636 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1612 = false ∨ valuation q 1636 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1636 = true := by
  have hs : count1621 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) + (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (l₂ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1621 q) 9 7 (meaning1489 q) (meaning1611 q) (meaning1636 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1611 = false ∨ valuation q 1636 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1636 = true := by
  have hs : count1621 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) + (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (l₂ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1621 q) 10 6 (meaning1490 q) (meaning1610 q) (meaning1636 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1610 = false ∨ valuation q 1636 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1636 = true := by
  have hs : count1621 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) + (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (l₂ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1609)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1621 q) 11 5 (meaning1491 q) (meaning1609 q) (meaning1636 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1609 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1609 = false ∨ valuation q 1636 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1636 = true := by
  have hs : count1621 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) + (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (l₂ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1621 q) 12 4 (meaning1492 q) (meaning1608 q) (meaning1636 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1608 = false ∨ valuation q 1636 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1636 = true := by
  have hs : count1621 q = (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) + (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (l₂ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1636)) (countLit q [-2, -3, -5, -8, -10, -11, -12, -15, -17, -18, -21, -24, -26, -29, -30, -31, -34, -36, -39, -40, -43, -44, -47, -51, -52, -54, -57, -58]) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85, -87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1621 q) 13 3 (meaning1493 q) (meaning1607 q) (meaning1636 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1607 = false ∨ valuation q 1636 = true := counterClause1109 (baseVal q)

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false := by
  rw [value1636]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1621 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 8 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value7, value8, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (67 : Vertex) (194 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 11 = false ∨ valuation q 44 = false ∨ valuation q 49 = false := by
  rw [value7, value11, value44, value49]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (66 : Vertex) (74 : Vertex) (194 : Vertex) (202 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 48 = false ∨ valuation q 60 = false := by
  rw [value10, value19, value48, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (73 : Vertex) (89 : Vertex) (201 : Vertex) (217 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 48 = false ∨ valuation q 71 = false ∨ valuation q 101 = false := by
  rw [value10, value48, value71, value101]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (73 : Vertex) (201 : Vertex) (329 : Vertex) (457 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 13 = false ∨ valuation q 49 = false ∨ valuation q 52 = false := by
  rw [value11, value13, value49, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (74 : Vertex) (78 : Vertex) (202 : Vertex) (206 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 19 = false ∨ valuation q 20 = false ∨ valuation q 21 = false := by
  rw [value18, value19, value20, value21]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (88 : Vertex) (89 : Vertex) (90 : Vertex) (91 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value23, value24, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (134 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 44 = false ∨ valuation q 45 = false := by
  rw [value23, value24, value44, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (131 : Vertex) (194 : Vertex) (195 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 26 = false ∨ valuation q 30 = false ∨ valuation q 32 = false := by
  rw [value23, value26, value30, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (134 : Vertex) (138 : Vertex) (142 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 24 = false ∨ valuation q 27 = false ∨ valuation q 45 = false ∨ valuation q 47 = false := by
  rw [value24, value27, value45, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (135 : Vertex) (195 : Vertex) (199 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E168.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112168
