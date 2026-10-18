import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1538)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 1 1 (meaning1510 q) (meaning1530 q) (meaning1538 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1530 = false ∨ valuation q 1538 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1539)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 1 2 (meaning1510 q) (meaning1531 q) (meaning1539 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1531 = false ∨ valuation q 1539 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1540)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 1 3 (meaning1510 q) (meaning1532 q) (meaning1540 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1532 = false ∨ valuation q 1540 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1511)) (literal (valuationOf q) (1538)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 2 (meaning1511 q) (meaning1538 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1538 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1539)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 2 1 (meaning1511 q) (meaning1530 q) (meaning1539 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1530 = false ∨ valuation q 1539 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1540)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 2 2 (meaning1511 q) (meaning1531 q) (meaning1540 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1531 = false ∨ valuation q 1540 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1512)) (literal (valuationOf q) (1539)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 3 (meaning1512 q) (meaning1539 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1539 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1540)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 3 1 (meaning1512 q) (meaning1530 q) (meaning1540 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1530 = false ∨ valuation q 1540 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1541)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 3 2 (meaning1512 q) (meaning1531 q) (meaning1541 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1531 = false ∨ valuation q 1541 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1541)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 4 1 (meaning1513 q) (meaning1530 q) (meaning1541 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1530 = false ∨ valuation q 1541 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1542)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 4 2 (meaning1513 q) (meaning1531 q) (meaning1542 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1531 = false ∨ valuation q 1542 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1514)) (literal (valuationOf q) (1541)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 5 (meaning1514 q) (meaning1541 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1541 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1542 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1542)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 5 1 (meaning1514 q) (meaning1530 q) (meaning1542 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1530 = false ∨ valuation q 1542 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1543 = true := by
  have hs : count1537 q = (countLit q [-85, -87, -88, -90, -93, -95, -97]) + (countLit q [-98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-85, -87, -88, -90, -93, -95, -97]) (l₂ := [-98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1543)) (countLit q [-85, -87, -88, -90, -93, -95, -97]) (countLit q [-98, -101, -103, -104, -106, -109, -111]) (count1537 q) 5 2 (meaning1514 q) (meaning1531 q) (meaning1543 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1531 = false ∨ valuation q 1543 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1556 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1556)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 1 5 (meaning1483 q) (meaning1541 q) (meaning1556 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1541 = false ∨ valuation q 1556 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1554 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1484)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1554)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 2 2 (meaning1484 q) (meaning1538 q) (meaning1554 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1538 = false ∨ valuation q 1554 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1556 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1484)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1556)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 2 4 (meaning1484 q) (meaning1540 q) (meaning1556 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1540 = false ∨ valuation q 1556 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1554 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1554)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 3 1 (meaning1485 q) (meaning1537 q) (meaning1554 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1537 = false ∨ valuation q 1554 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1555 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1555)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 3 2 (meaning1485 q) (meaning1538 q) (meaning1555 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1538 = false ∨ valuation q 1555 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1556 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1556)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 3 3 (meaning1485 q) (meaning1539 q) (meaning1556 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1539 = false ∨ valuation q 1556 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1557 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1557)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 3 4 (meaning1485 q) (meaning1540 q) (meaning1557 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1540 = false ∨ valuation q 1557 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1558 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1558)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 3 5 (meaning1485 q) (meaning1541 q) (meaning1558 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1541 = false ∨ valuation q 1558 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1559 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1559)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 3 6 (meaning1485 q) (meaning1542 q) (meaning1559 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1542 = false ∨ valuation q 1559 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1560)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 3 7 (meaning1485 q) (meaning1543 q) (meaning1560 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1543 = false ∨ valuation q 1560 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1555 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1555)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 4 1 (meaning1486 q) (meaning1537 q) (meaning1555 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1537 = false ∨ valuation q 1555 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1556 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1556)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 4 2 (meaning1486 q) (meaning1538 q) (meaning1556 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1538 = false ∨ valuation q 1556 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1557 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1557)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 4 3 (meaning1486 q) (meaning1539 q) (meaning1557 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1539 = false ∨ valuation q 1557 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1558 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1558)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 4 4 (meaning1486 q) (meaning1540 q) (meaning1558 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1540 = false ∨ valuation q 1558 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1559 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1559)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 4 5 (meaning1486 q) (meaning1541 q) (meaning1559 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1541 = false ∨ valuation q 1559 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1560)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 4 6 (meaning1486 q) (meaning1542 q) (meaning1560 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1542 = false ∨ valuation q 1560 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1556 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1556)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 5 1 (meaning1487 q) (meaning1537 q) (meaning1556 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1537 = false ∨ valuation q 1556 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1557 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1557)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 5 2 (meaning1487 q) (meaning1538 q) (meaning1557 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1538 = false ∨ valuation q 1557 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E161.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112161
