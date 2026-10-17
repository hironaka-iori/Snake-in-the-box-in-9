import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-74]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1573)) (countLit q [-74]) (countLit q [-77]) (count1573 q) 1 (meaningNeg74 q) (meaning1573 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1573 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1574 = true := by
  have hs : count1573 q = (countLit q [-74]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1574)) (countLit q [-74]) (countLit q [-77]) (count1573 q) 1 1 (meaningNeg74 q) (meaningNeg77 q) (meaning1574 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 77 = true ∨ valuation q 1574 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1575)) (countLit q [-78]) (countLit q [-80]) (count1575 q) 1 (meaningNeg80 q) (meaning1575 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1575 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-74, -77]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -77]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1575)) (literal (valuationOf q) (1577)) (countLit q [-74, -77]) (countLit q [-78, -80]) (count1577 q) 1 (meaning1575 q) (meaning1577 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1577 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-74, -77]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -77]) (l₂ := [-78, -80])
  have hm := merge_left (literal (valuationOf q) (1573)) (literal (valuationOf q) (1577)) (countLit q [-74, -77]) (countLit q [-78, -80]) (count1577 q) 1 (meaning1573 q) (meaning1577 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1577 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1578 = true := by
  have hs : count1577 q = (countLit q [-74, -77]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -77]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1578)) (countLit q [-74, -77]) (countLit q [-78, -80]) (count1577 q) 1 1 (meaning1573 q) (meaning1575 q) (meaning1578 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1575 = false ∨ valuation q 1578 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1578 = true := by
  have hs : count1577 q = (countLit q [-74, -77]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -77]) (l₂ := [-78, -80])
  have hm := merge_left (literal (valuationOf q) (1574)) (literal (valuationOf q) (1578)) (countLit q [-74, -77]) (countLit q [-78, -80]) (count1577 q) 2 (meaning1574 q) (meaning1578 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1578 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1579 = true := by
  have hs : count1577 q = (countLit q [-74, -77]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-74, -77]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1575)) (literal (valuationOf q) (1579)) (countLit q [-74, -77]) (countLit q [-78, -80]) (count1577 q) 2 1 (meaning1574 q) (meaning1575 q) (meaning1579 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1575 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1575 = false ∨ valuation q 1579 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1581)) (countLit q [-82]) (countLit q [-84]) (count1581 q) 1 (meaningNeg84 q) (meaning1581 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1581 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1581)) (countLit q [-82]) (countLit q [-84]) (count1581 q) 1 (meaningNeg82 q) (meaning1581 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1581 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1582 = true := by
  have hs : count1581 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1582)) (countLit q [-82]) (countLit q [-84]) (count1581 q) 1 1 (meaningNeg82 q) (meaningNeg84 q) (meaning1582 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 84 = true ∨ valuation q 1582 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1583)) (countLit q [-86]) (countLit q [-87]) (count1583 q) 1 (meaningNeg87 q) (meaning1583 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1583 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1583)) (countLit q [-86]) (countLit q [-87]) (count1583 q) 1 (meaningNeg86 q) (meaning1583 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1583 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1584)) (countLit q [-86]) (countLit q [-87]) (count1583 q) 1 1 (meaningNeg86 q) (meaningNeg87 q) (meaning1584 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 1584 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1585 q) 1 (meaning1583 q) (meaning1585 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1584)) (literal (valuationOf q) (1586)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1585 q) 2 (meaning1584 q) (meaning1586 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1586 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_left (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1585 q) 1 (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1586)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1585 q) 1 1 (meaning1581 q) (meaning1583 q) (meaning1586 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = false ∨ valuation q 1586 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1586)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1585 q) 2 (meaning1582 q) (meaning1586 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1586 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1585 q = (countLit q [-82, -84]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -84]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-82, -84]) (countLit q [-86, -87]) (count1585 q) 2 1 (meaning1582 q) (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1583 = false ∨ valuation q 1587 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_right (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 1 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_right (literal (valuationOf q) (1586)) (literal (valuationOf q) (1590)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 2 (meaning1586 q) (meaning1590 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1590 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 3 (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1591 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1577)) (literal (valuationOf q) (1589)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 1 (meaning1577 q) (meaning1589 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1589 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1590)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 1 1 (meaning1577 q) (meaning1585 q) (meaning1590 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1585 = false ∨ valuation q 1590 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1591)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 1 2 (meaning1577 q) (meaning1586 q) (meaning1591 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1586 = false ∨ valuation q 1591 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1592)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 1 3 (meaning1577 q) (meaning1587 q) (meaning1592 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1587 = false ∨ valuation q 1592 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1578)) (literal (valuationOf q) (1590)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 2 (meaning1578 q) (meaning1590 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1590 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1591)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 2 1 (meaning1578 q) (meaning1585 q) (meaning1591 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1585 = false ∨ valuation q 1591 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1592 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1592)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 2 2 (meaning1578 q) (meaning1586 q) (meaning1592 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1586 = false ∨ valuation q 1592 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1593)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 2 3 (meaning1578 q) (meaning1587 q) (meaning1593 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1587 = false ∨ valuation q 1593 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-74, -77, -78, -80]) + (countLit q [-82, -84, -86, -87]) := List.countP_append (p := literal q) (l₁ := [-74, -77, -78, -80]) (l₂ := [-82, -84, -86, -87])
  have hm := merge_left (literal (valuationOf q) (1579)) (literal (valuationOf q) (1591)) (countLit q [-74, -77, -78, -80]) (countLit q [-82, -84, -86, -87]) (count1589 q) 3 (meaning1579 q) (meaning1591 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1591 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E158.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112158
