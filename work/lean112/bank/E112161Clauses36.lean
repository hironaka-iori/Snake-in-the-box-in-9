import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1558 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1558)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 5 3 (meaning1487 q) (meaning1539 q) (meaning1558 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1539 = false ∨ valuation q 1558 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1559 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1559)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 5 4 (meaning1487 q) (meaning1540 q) (meaning1559 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1540 = false ∨ valuation q 1559 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1557 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1557)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 6 1 (meaning1488 q) (meaning1537 q) (meaning1557 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1537 = false ∨ valuation q 1557 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1558 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1558)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 6 2 (meaning1488 q) (meaning1538 q) (meaning1558 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1538 = false ∨ valuation q 1558 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1559 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1559)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 6 3 (meaning1488 q) (meaning1539 q) (meaning1559 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1539 = false ∨ valuation q 1559 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1560 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1560)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 6 4 (meaning1488 q) (meaning1540 q) (meaning1560 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1540 = false ∨ valuation q 1560 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1558 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1558)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 7 1 (meaning1489 q) (meaning1537 q) (meaning1558 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1537 = false ∨ valuation q 1558 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1559 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1559)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 7 2 (meaning1489 q) (meaning1538 q) (meaning1559 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1538 = false ∨ valuation q 1559 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1560 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1560)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 7 3 (meaning1489 q) (meaning1539 q) (meaning1560 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1539 = false ∨ valuation q 1560 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1559 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1559)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 8 1 (meaning1490 q) (meaning1537 q) (meaning1559 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1537 = false ∨ valuation q 1559 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1559 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1491)) (literal (valuationOf q) (1559)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 9 (meaning1491 q) (meaning1559 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1559 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1560 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1560)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 9 1 (meaning1491 q) (meaning1537 q) (meaning1560 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1537 = false ∨ valuation q 1560 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1560 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1492)) (literal (valuationOf q) (1560)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 10 (meaning1492 q) (meaning1560 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1560 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1561 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1561)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 10 1 (meaning1492 q) (meaning1537 q) (meaning1561 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1537 = false ∨ valuation q 1561 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1561 = true := by
  have hs : count1551 q = (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) + (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (l₂ := [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_left (literal (valuationOf q) (1493)) (literal (valuationOf q) (1561)) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81]) (countLit q [-85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1551 q) 11 (meaning1493 q) (meaning1561 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1561 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1431 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1582 = true := by
  have hs : count1567 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) + (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (l₂ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1431)) (literal (valuationOf q) (1561)) (literal (valuationOf q) (1582)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1567 q) 5 11 (meaning1431 q) (meaning1561 q) (meaning1582 q) hs
  change valuationOf q 1431 = false ∨ valuationOf q 1561 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1431 = false ∨ valuation q 1561 = false ∨ valuation q 1582 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1582 = true := by
  have hs : count1567 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) + (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (l₂ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1582)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1567 q) 6 10 (meaning1432 q) (meaning1560 q) (meaning1582 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1560 = false ∨ valuation q 1582 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1582 = true := by
  have hs : count1567 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) + (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (l₂ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1582)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1567 q) 7 9 (meaning1433 q) (meaning1559 q) (meaning1582 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1559 = false ∨ valuation q 1582 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1582 = true := by
  have hs : count1567 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) + (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (l₂ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1582)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1567 q) 8 8 (meaning1434 q) (meaning1558 q) (meaning1582 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1558 = false ∨ valuation q 1582 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1582 = true := by
  have hs : count1567 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) + (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (l₂ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1582)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1567 q) 9 7 (meaning1435 q) (meaning1557 q) (meaning1582 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1557 = false ∨ valuation q 1582 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1582 = true := by
  have hs : count1567 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) + (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (l₂ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1436)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1582)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1567 q) 10 6 (meaning1436 q) (meaning1556 q) (meaning1582 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1556 = false ∨ valuation q 1582 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1582 = true := by
  have hs : count1567 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) + (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (l₂ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1582)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1567 q) 11 5 (meaning1437 q) (meaning1555 q) (meaning1582 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1555 = false ∨ valuation q 1582 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1582 = true := by
  have hs : count1567 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) + (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (l₂ := [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1582)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29, -30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (countLit q [-55, -57, -58, -62, -63, -67, -69, -70, -72, -74, -76, -78, -80, -81, -85, -87, -88, -90, -93, -95, -97, -98, -101, -103, -104, -106, -109, -111]) (count1567 q) 12 4 (meaning1438 q) (meaning1554 q) (meaning1582 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1554 = false ∨ valuation q 1582 = true := counterClause1175 (baseVal q)

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false := by
  rw [value1582]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1567 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 3 = false ∨ valuation q 44 = false ∨ valuation q 47 = false := by
  rw [value2, value3, value44, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (2 : Vertex) (6 : Vertex) (258 : Vertex) (262 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 15 = false := by
  rw [value11, value12, value14, value15]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (133 : Vertex) (135 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 16 = false ∨ valuation q 18 = false := by
  rw [value11, value12, value16, value18]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (129 : Vertex) (131 : Vertex) (137 : Vertex) (139 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 18 = false ∨ valuation q 84 = false ∨ valuation q 85 = false := by
  rw [value17, value18, value84, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (138 : Vertex) (139 : Vertex) (394 : Vertex) (395 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value20, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (146 : Vertex) (148 : Vertex) (150 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 25 = false ∨ valuation q 27 = false := by
  rw [value20, value21, value25, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (144 : Vertex) (146 : Vertex) (152 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 43 = false ∨ valuation q 45 = false ∨ valuation q 50 = false ∨ valuation q 52 = false := by
  rw [value43, value45, value50, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (259 : Vertex) (265 : Vertex) (267 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 48 = false ∨ valuation q 52 = false ∨ valuation q 53 = false := by
  rw [value45, value48, value52, value53]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (259 : Vertex) (263 : Vertex) (267 : Vertex) (271 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E161.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112161
