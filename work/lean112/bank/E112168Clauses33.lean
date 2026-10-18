import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-101, -102, -104]) + (countLit q [-107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-101, -102, -104]) (l₂ := [-107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1585)) (countLit q [-101, -102, -104]) (countLit q [-107, -110, -111, -113]) (count1584 q) 1 1 (meaning1573 q) (meaning1580 q) (meaning1585 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1580 = false ∨ valuation q 1585 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-101, -102, -104]) + (countLit q [-107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-101, -102, -104]) (l₂ := [-107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1586)) (countLit q [-101, -102, -104]) (countLit q [-107, -110, -111, -113]) (count1584 q) 1 2 (meaning1573 q) (meaning1581 q) (meaning1586 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1581 = false ∨ valuation q 1586 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1585 = true := by
  have hs : count1584 q = (countLit q [-101, -102, -104]) + (countLit q [-107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-101, -102, -104]) (l₂ := [-107, -110, -111, -113])
  have hm := merge_left (literal (valuationOf q) (1574)) (literal (valuationOf q) (1585)) (countLit q [-101, -102, -104]) (countLit q [-107, -110, -111, -113]) (count1584 q) 2 (meaning1574 q) (meaning1585 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1585 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-101, -102, -104]) + (countLit q [-107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-101, -102, -104]) (l₂ := [-107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1586)) (countLit q [-101, -102, -104]) (countLit q [-107, -110, -111, -113]) (count1584 q) 2 1 (meaning1574 q) (meaning1580 q) (meaning1586 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1580 = false ∨ valuation q 1586 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1586 = true := by
  have hs : count1584 q = (countLit q [-101, -102, -104]) + (countLit q [-107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-101, -102, -104]) (l₂ := [-107, -110, -111, -113])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1586)) (countLit q [-101, -102, -104]) (countLit q [-107, -110, -111, -113]) (count1584 q) 3 (meaning1575 q) (meaning1586 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1586 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_right (literal (valuationOf q) (1584)) (literal (valuationOf q) (1591)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 1 (meaning1584 q) (meaning1591 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1591 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1592)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 1 1 (meaning1564 q) (meaning1584 q) (meaning1592 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1584 = false ∨ valuation q 1592 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1593)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 1 2 (meaning1564 q) (meaning1585 q) (meaning1593 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1585 = false ∨ valuation q 1593 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1564)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1594)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 1 3 (meaning1564 q) (meaning1586 q) (meaning1594 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1586 = false ∨ valuation q 1594 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_left (literal (valuationOf q) (1565)) (literal (valuationOf q) (1592)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 2 (meaning1565 q) (meaning1592 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1592 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1593)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 2 1 (meaning1565 q) (meaning1584 q) (meaning1593 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1584 = false ∨ valuation q 1593 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1565)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1594)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 2 2 (meaning1565 q) (meaning1585 q) (meaning1594 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1585 = false ∨ valuation q 1594 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1594)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 3 1 (meaning1566 q) (meaning1584 q) (meaning1594 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1584 = false ∨ valuation q 1594 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1595 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1566)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1595)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 3 2 (meaning1566 q) (meaning1585 q) (meaning1595 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1585 = false ∨ valuation q 1595 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1595 = true := by
  have hs : count1591 q = (countLit q [-87, -91, -92, -93, -94, -98, -100]) + (countLit q [-101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-87, -91, -92, -93, -94, -98, -100]) (l₂ := [-101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1595)) (countLit q [-87, -91, -92, -93, -94, -98, -100]) (countLit q [-101, -102, -104, -107, -110, -111, -113]) (count1591 q) 4 1 (meaning1567 q) (meaning1584 q) (meaning1595 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1584 = false ∨ valuation q 1595 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1609 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_right (literal (valuationOf q) (1595)) (literal (valuationOf q) (1609)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 5 (meaning1595 q) (meaning1609 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1609 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1607)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 1 2 (meaning1537 q) (meaning1592 q) (meaning1607 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1592 = false ∨ valuation q 1607 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1608 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1608)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 1 3 (meaning1537 q) (meaning1593 q) (meaning1608 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1593 = false ∨ valuation q 1608 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1609 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1609)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 1 4 (meaning1537 q) (meaning1594 q) (meaning1609 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1594 = false ∨ valuation q 1609 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1610 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1610)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 1 5 (meaning1537 q) (meaning1595 q) (meaning1610 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1595 = false ∨ valuation q 1610 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1608 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1608)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 2 2 (meaning1538 q) (meaning1592 q) (meaning1608 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1592 = false ∨ valuation q 1608 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1609 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1609)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 2 3 (meaning1538 q) (meaning1593 q) (meaning1609 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1593 = false ∨ valuation q 1609 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1610 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1610)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 2 4 (meaning1538 q) (meaning1594 q) (meaning1610 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1594 = false ∨ valuation q 1610 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1611 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1611)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 2 5 (meaning1538 q) (meaning1595 q) (meaning1611 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1595 = false ∨ valuation q 1611 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1608 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1608)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 3 1 (meaning1539 q) (meaning1591 q) (meaning1608 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1591 = false ∨ valuation q 1608 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1609 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1609)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 3 2 (meaning1539 q) (meaning1592 q) (meaning1609 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1592 = false ∨ valuation q 1609 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1610 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1610)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 3 3 (meaning1539 q) (meaning1593 q) (meaning1610 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1593 = false ∨ valuation q 1610 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1611 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1611)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 3 4 (meaning1539 q) (meaning1594 q) (meaning1611 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1594 = false ∨ valuation q 1611 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1612 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1595)) (literal (valuationOf q) (1612)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 3 5 (meaning1539 q) (meaning1595 q) (meaning1612 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1595 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1595 = false ∨ valuation q 1612 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1610 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1610)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 4 2 (meaning1540 q) (meaning1592 q) (meaning1610 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1592 = false ∨ valuation q 1610 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1611 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1611)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 4 3 (meaning1540 q) (meaning1593 q) (meaning1611 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1593 = false ∨ valuation q 1611 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1612 = true := by
  have hs : count1605 q = (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) + (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (l₂ := [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1612)) (countLit q [-60, -61, -62, -66, -68, -69, -70, -72, -76, -77, -78, -82, -84, -85]) (countLit q [-87, -91, -92, -93, -94, -98, -100, -101, -102, -104, -107, -110, -111, -113]) (count1605 q) 4 4 (meaning1540 q) (meaning1594 q) (meaning1612 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1594 = false ∨ valuation q 1612 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E168.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112168
