import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1640 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1640)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 9 4 (meaning1557 q) (meaning1615 q) (meaning1640 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1615 = false ∨ valuation q 1640 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1641)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 9 5 (meaning1557 q) (meaning1616 q) (meaning1641 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1616 = false ∨ valuation q 1641 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1642)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 9 6 (meaning1557 q) (meaning1617 q) (meaning1642 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1617 = false ∨ valuation q 1642 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1641 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1641)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 10 4 (meaning1558 q) (meaning1615 q) (meaning1641 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1615 = false ∨ valuation q 1641 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1642 = true := by
  have hs : count1628 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) + (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (l₂ := [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1642)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26]) (countLit q [-28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (count1628 q) 10 5 (meaning1558 q) (meaning1616 q) (meaning1642 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1616 = false ∨ valuation q 1642 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1650)) (countLit q [-62]) (countLit q [-63]) (count1650 q) 1 (meaningNeg63 q) (meaning1650 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1650 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1650)) (countLit q [-62]) (countLit q [-63]) (count1650 q) 1 (meaningNeg62 q) (meaning1650 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1650 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-62]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1651)) (countLit q [-62]) (countLit q [-63]) (count1650 q) 1 1 (meaningNeg62 q) (meaningNeg63 q) (meaning1651 q) hs
  change (! (valuationOf q 62)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 63 = true ∨ valuation q 1651 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1650)) (literal (valuationOf q) (1652)) (countLit q [-60]) (countLit q [-62, -63]) (count1652 q) 1 (meaning1650 q) (meaning1652 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1652 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1651)) (literal (valuationOf q) (1653)) (countLit q [-60]) (countLit q [-62, -63]) (count1652 q) 2 (meaning1651 q) (meaning1653 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1653 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1653)) (countLit q [-60]) (countLit q [-62, -63]) (count1652 q) 1 1 (meaningNeg60 q) (meaning1650 q) (meaning1653 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1650 = false ∨ valuation q 1653 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1651 = false ∨ valuationOf q 1654 = true := by
  have hs : count1652 q = (countLit q [-60]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1654)) (countLit q [-60]) (countLit q [-62, -63]) (count1652 q) 1 2 (meaningNeg60 q) (meaning1651 q) (meaning1654 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1651 = false ∨ valuation q 1654 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1655)) (countLit q [-65]) (countLit q [-66]) (count1655 q) 1 (meaningNeg66 q) (meaning1655 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1655 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1655)) (countLit q [-65]) (countLit q [-66]) (count1655 q) 1 (meaningNeg65 q) (meaning1655 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1655 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1656)) (countLit q [-65]) (countLit q [-66]) (count1655 q) 1 1 (meaningNeg65 q) (meaningNeg66 q) (meaning1656 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 66 = true ∨ valuation q 1656 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1657)) (countLit q [-68]) (countLit q [-71]) (count1657 q) 1 (meaningNeg71 q) (meaning1657 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1657 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1657)) (countLit q [-68]) (countLit q [-71]) (count1657 q) 1 (meaningNeg68 q) (meaning1657 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1657 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-68]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1658)) (countLit q [-68]) (countLit q [-71]) (count1657 q) 1 1 (meaningNeg68 q) (meaningNeg71 q) (meaning1658 q) hs
  change (! (valuationOf q 68)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 71 = true ∨ valuation q 1658 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-65, -66]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -71])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1659)) (countLit q [-65, -66]) (countLit q [-68, -71]) (count1659 q) 1 (meaning1657 q) (meaning1659 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1659 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-65, -66]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -71])
  have hm := merge_right (literal (valuationOf q) (1658)) (literal (valuationOf q) (1660)) (countLit q [-65, -66]) (countLit q [-68, -71]) (count1659 q) 2 (meaning1658 q) (meaning1660 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1660 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-65, -66]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -71])
  have hm := merge_left (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-65, -66]) (countLit q [-68, -71]) (count1659 q) 1 (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1659 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-65, -66]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -71])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1660)) (countLit q [-65, -66]) (countLit q [-68, -71]) (count1659 q) 1 1 (meaning1655 q) (meaning1657 q) (meaning1660 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1657 = false ∨ valuation q 1660 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-65, -66]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -71])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1661)) (countLit q [-65, -66]) (countLit q [-68, -71]) (count1659 q) 1 2 (meaning1655 q) (meaning1658 q) (meaning1661 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1658 = false ∨ valuation q 1661 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-65, -66]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -71])
  have hm := merge_left (literal (valuationOf q) (1656)) (literal (valuationOf q) (1660)) (countLit q [-65, -66]) (countLit q [-68, -71]) (count1659 q) 2 (meaning1656 q) (meaning1660 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1660 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-65, -66]) + (countLit q [-68, -71]) := List.countP_append (p := literal q) (l₁ := [-65, -66]) (l₂ := [-68, -71])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1661)) (countLit q [-65, -66]) (countLit q [-68, -71]) (count1659 q) 2 1 (meaning1656 q) (meaning1657 q) (meaning1661 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1657 = false ∨ valuation q 1661 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_right (literal (valuationOf q) (1659)) (literal (valuationOf q) (1663)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 1 (meaning1659 q) (meaning1663 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1663 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1664)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 1 1 (meaning1652 q) (meaning1659 q) (meaning1664 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1659 = false ∨ valuation q 1664 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1665 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1665)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 1 2 (meaning1652 q) (meaning1660 q) (meaning1665 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1660 = false ∨ valuation q 1665 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1666)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 1 3 (meaning1652 q) (meaning1661 q) (meaning1666 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1661 = false ∨ valuation q 1666 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1665 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1665)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 2 1 (meaning1653 q) (meaning1659 q) (meaning1665 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1659 = false ∨ valuation q 1665 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1666)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 2 2 (meaning1653 q) (meaning1660 q) (meaning1666 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1660 = false ∨ valuation q 1666 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1667)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 2 3 (meaning1653 q) (meaning1661 q) (meaning1667 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1661 = false ∨ valuation q 1667 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E008.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112008
