import E112004Semantics
import B112E004Inputs
namespace Snake9.Regrowth.E112004
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1548)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 4 1 (meaning1516 q) (meaning1536 q) (meaning1548 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1536 = false ∨ valuation q 1548 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1549)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 4 2 (meaning1516 q) (meaning1537 q) (meaning1549 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1537 = false ∨ valuation q 1549 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1550)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 4 3 (meaning1516 q) (meaning1538 q) (meaning1550 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1538 = false ∨ valuation q 1550 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1551)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 4 4 (meaning1516 q) (meaning1539 q) (meaning1551 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1539 = false ∨ valuation q 1551 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1552)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 4 5 (meaning1516 q) (meaning1540 q) (meaning1552 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1540 = false ∨ valuation q 1552 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1553 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1553)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 4 6 (meaning1516 q) (meaning1541 q) (meaning1553 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1541 = false ∨ valuation q 1553 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1554)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 4 7 (meaning1516 q) (meaning1542 q) (meaning1554 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1542 = false ∨ valuation q 1554 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1548 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_left (literal (valuationOf q) (1517)) (literal (valuationOf q) (1548)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 5 (meaning1517 q) (meaning1548 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1548 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1549 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1549)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 5 1 (meaning1517 q) (meaning1536 q) (meaning1549 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1536 = false ∨ valuation q 1549 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1550 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1550)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 5 2 (meaning1517 q) (meaning1537 q) (meaning1550 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1537 = false ∨ valuation q 1550 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1551)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 5 3 (meaning1517 q) (meaning1538 q) (meaning1551 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1538 = false ∨ valuation q 1551 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1552)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 5 4 (meaning1517 q) (meaning1539 q) (meaning1552 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1539 = false ∨ valuation q 1552 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1553 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1553)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 5 5 (meaning1517 q) (meaning1540 q) (meaning1553 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1540 = false ∨ valuation q 1553 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1554 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1554)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 5 6 (meaning1517 q) (meaning1541 q) (meaning1554 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1541 = false ∨ valuation q 1554 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1551 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1551)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 6 2 (meaning1518 q) (meaning1537 q) (meaning1551 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1537 = false ∨ valuation q 1551 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1552 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1552)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 6 3 (meaning1518 q) (meaning1538 q) (meaning1552 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1538 = false ∨ valuation q 1552 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1553 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1553)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 6 4 (meaning1518 q) (meaning1539 q) (meaning1553 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1539 = false ∨ valuation q 1553 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1554 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1554)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 6 5 (meaning1518 q) (meaning1540 q) (meaning1554 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1540 = false ∨ valuation q 1554 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1555 = true := by
  have hs : count1544 q = (countLit q [-32, -35, -36, -38, -40, -42, -44]) + (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -36, -38, -40, -42, -44]) (l₂ := [-46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1555)) (countLit q [-32, -35, -36, -38, -40, -42, -44]) (countLit q [-46, -48, -51, -52, -53, -56, -59, -60]) (count1544 q) 6 6 (meaning1518 q) (meaning1541 q) (meaning1555 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1541 = false ∨ valuation q 1555 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1569)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 2 9 (meaning1486 q) (meaning1552 q) (meaning1569 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1552 = false ∨ valuation q 1569 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1564 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1564)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 3 (meaning1487 q) (meaning1546 q) (meaning1564 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1546 = false ∨ valuation q 1564 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1565 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1565)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 4 (meaning1487 q) (meaning1547 q) (meaning1565 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1547 = false ∨ valuation q 1565 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1566 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1566)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 5 (meaning1487 q) (meaning1548 q) (meaning1566 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1548 = false ∨ valuation q 1566 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1567 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1567)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 6 (meaning1487 q) (meaning1549 q) (meaning1567 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1549 = false ∨ valuation q 1567 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1568 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1568)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 7 (meaning1487 q) (meaning1550 q) (meaning1568 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1550 = false ∨ valuation q 1568 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1569 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1569)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 8 (meaning1487 q) (meaning1551 q) (meaning1569 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1551 = false ∨ valuation q 1569 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1570 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1570)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 9 (meaning1487 q) (meaning1552 q) (meaning1570 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1552 = false ∨ valuation q 1570 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1571 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1571)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 10 (meaning1487 q) (meaning1553 q) (meaning1571 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1553 = false ∨ valuation q 1571 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1572 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1572)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 11 (meaning1487 q) (meaning1554 q) (meaning1572 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1554 = false ∨ valuation q 1572 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1573 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1573)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 3 12 (meaning1487 q) (meaning1555 q) (meaning1573 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1555 = false ∨ valuation q 1573 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1565 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1565)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 4 3 (meaning1488 q) (meaning1546 q) (meaning1565 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1546 = false ∨ valuation q 1565 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1566 = true := by
  have hs : count1559 q = (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) + (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (l₂ := [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1566)) (countLit q [-2, -3, -5, -6, -12, -13, -15, -18, -20, -21, -22, -24, -26, -28, -30]) (countLit q [-32, -35, -36, -38, -40, -42, -44, -46, -48, -51, -52, -53, -56, -59, -60]) (count1559 q) 4 4 (meaning1488 q) (meaning1547 q) (meaning1566 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1547 = false ∨ valuation q 1566 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E004.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112004
