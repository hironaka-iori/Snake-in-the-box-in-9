import E112105Semantics
import B112E105Inputs
namespace Snake9.Regrowth.E112105
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1543 = true := by
  have hs : count1543 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1543)) (countLit q [-28]) (countLit q [-31]) (count1543 q) 1 (meaningNeg28 q) (meaning1543 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1543 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1544 = true := by
  have hs : count1543 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1544)) (countLit q [-28]) (countLit q [-31]) (count1543 q) 1 1 (meaningNeg28 q) (meaningNeg31 q) (meaning1544 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 1544 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1545 = true := by
  have hs : count1545 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (1543)) (literal (valuationOf q) (1545)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count1545 q) 1 (meaning1543 q) (meaning1545 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1545 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1546 = true := by
  have hs : count1545 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (1544)) (literal (valuationOf q) (1546)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count1545 q) 2 (meaning1544 q) (meaning1546 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1546 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1545 = true := by
  have hs : count1545 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_left (literal (valuationOf q) (1541)) (literal (valuationOf q) (1545)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count1545 q) 1 (meaning1541 q) (meaning1545 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1545 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1546 = true := by
  have hs : count1545 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1546)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count1545 q) 1 1 (meaning1541 q) (meaning1543 q) (meaning1546 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1543 = false ∨ valuation q 1546 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1547 = true := by
  have hs : count1545 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1541)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1547)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count1545 q) 1 2 (meaning1541 q) (meaning1544 q) (meaning1547 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1544 = false ∨ valuation q 1547 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1546 = true := by
  have hs : count1545 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_left (literal (valuationOf q) (1542)) (literal (valuationOf q) (1546)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count1545 q) 2 (meaning1542 q) (meaning1546 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1546 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1547 = true := by
  have hs : count1545 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1547)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count1545 q) 2 1 (meaning1542 q) (meaning1543 q) (meaning1547 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1543 = false ∨ valuation q 1547 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1542 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-25, -27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -27]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1542)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1548)) (countLit q [-25, -27]) (countLit q [-28, -31]) (count1545 q) 2 2 (meaning1542 q) (meaning1544 q) (meaning1548 q) hs
  change valuationOf q 1542 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1542 = false ∨ valuation q 1544 = false ∨ valuation q 1548 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1545)) (literal (valuationOf q) (1549)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 1 (meaning1545 q) (meaning1549 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1549 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1546)) (literal (valuationOf q) (1550)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 2 (meaning1546 q) (meaning1550 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1550 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1551 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1547)) (literal (valuationOf q) (1551)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 3 (meaning1547 q) (meaning1551 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1551 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1548)) (literal (valuationOf q) (1552)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 4 (meaning1548 q) (meaning1552 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1552 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1549 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1537)) (literal (valuationOf q) (1549)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 1 (meaning1537 q) (meaning1549 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1549 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1550)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 1 1 (meaning1537 q) (meaning1545 q) (meaning1550 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1545 = false ∨ valuation q 1550 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1551 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1551)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 1 2 (meaning1537 q) (meaning1546 q) (meaning1551 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1546 = false ∨ valuation q 1551 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1552)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 1 3 (meaning1537 q) (meaning1547 q) (meaning1552 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1547 = false ∨ valuation q 1552 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1553)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 1 4 (meaning1537 q) (meaning1548 q) (meaning1553 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1548 = false ∨ valuation q 1553 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1550 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1538)) (literal (valuationOf q) (1550)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 2 (meaning1538 q) (meaning1550 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1550 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1551 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1551)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 2 1 (meaning1538 q) (meaning1545 q) (meaning1551 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1545 = false ∨ valuation q 1551 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1552)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 2 2 (meaning1538 q) (meaning1546 q) (meaning1552 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1546 = false ∨ valuation q 1552 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1538)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1553)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 2 3 (meaning1538 q) (meaning1547 q) (meaning1553 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1547 = false ∨ valuation q 1553 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1551 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1539)) (literal (valuationOf q) (1551)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 3 (meaning1539 q) (meaning1551 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1551 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1552)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 3 1 (meaning1539 q) (meaning1545 q) (meaning1552 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1545 = false ∨ valuation q 1552 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1553)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 3 2 (meaning1539 q) (meaning1546 q) (meaning1553 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1546 = false ∨ valuation q 1553 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1554)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 3 3 (meaning1539 q) (meaning1547 q) (meaning1554 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1547 = false ∨ valuation q 1554 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1552 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1540)) (literal (valuationOf q) (1552)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 4 (meaning1540 q) (meaning1552 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1552 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1553 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1553)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 4 1 (meaning1540 q) (meaning1545 q) (meaning1553 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1545 = false ∨ valuation q 1553 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1554 = true := by
  have hs : count1549 q = (countLit q [-17, -20, -22, -23]) + (countLit q [-25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -20, -22, -23]) (l₂ := [-25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1540)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1554)) (countLit q [-17, -20, -22, -23]) (countLit q [-25, -27, -28, -31]) (count1549 q) 4 2 (meaning1540 q) (meaning1546 q) (meaning1554 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1546 = false ∨ valuation q 1554 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1557)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 1 (meaning1526 q) (meaning1557 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1557 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-2, -4, -6, -7, -10, -13, -16]) + (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -7, -10, -13, -16]) (l₂ := [-17, -20, -22, -23, -25, -27, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1558)) (countLit q [-2, -4, -6, -7, -10, -13, -16]) (countLit q [-17, -20, -22, -23, -25, -27, -28, -31]) (count1557 q) 1 1 (meaning1526 q) (meaning1549 q) (meaning1558 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1549 = false ∨ valuation q 1558 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E105.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112105
