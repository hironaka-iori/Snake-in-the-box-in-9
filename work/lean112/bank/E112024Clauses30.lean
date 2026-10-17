import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1543 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_left (literal (valuationOf q) (1531)) (literal (valuationOf q) (1543)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 2 (meaning1531 q) (meaning1543 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1543 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1544)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 2 1 (meaning1531 q) (meaning1538 q) (meaning1544 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1538 = false ∨ valuation q 1544 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1545 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1545)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 2 2 (meaning1531 q) (meaning1539 q) (meaning1545 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1539 = false ∨ valuation q 1545 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1546 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1546)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 2 3 (meaning1531 q) (meaning1540 q) (meaning1546 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1540 = false ∨ valuation q 1546 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1544 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_left (literal (valuationOf q) (1532)) (literal (valuationOf q) (1544)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 3 (meaning1532 q) (meaning1544 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1544 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1545)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 3 1 (meaning1532 q) (meaning1538 q) (meaning1545 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1538 = false ∨ valuation q 1545 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1546 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1546)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 3 2 (meaning1532 q) (meaning1539 q) (meaning1546 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1539 = false ∨ valuation q 1546 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1547 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1547)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 3 3 (meaning1532 q) (meaning1540 q) (meaning1547 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1540 = false ∨ valuation q 1547 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1546 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1546)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 4 1 (meaning1533 q) (meaning1538 q) (meaning1546 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1538 = false ∨ valuation q 1546 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1547 = true := by
  have hs : count1542 q = (countLit q [-43, -44, -47, -50]) + (countLit q [-53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -47, -50]) (l₂ := [-53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1533)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1547)) (countLit q [-43, -44, -47, -50]) (countLit q [-53, -54, -55, -56]) (count1542 q) 4 2 (meaning1533 q) (meaning1539 q) (meaning1547 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1539 = false ∨ valuation q 1547 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1551 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1551)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 1 1 (meaning1518 q) (meaning1542 q) (meaning1551 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1542 = false ∨ valuation q 1551 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1552 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1552)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 1 2 (meaning1518 q) (meaning1543 q) (meaning1552 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1543 = false ∨ valuation q 1552 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1553 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1553)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 1 3 (meaning1518 q) (meaning1544 q) (meaning1553 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1544 = false ∨ valuation q 1553 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1554 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1554)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 1 4 (meaning1518 q) (meaning1545 q) (meaning1554 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1545 = false ∨ valuation q 1554 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1555 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1555)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 1 5 (meaning1518 q) (meaning1546 q) (meaning1555 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1546 = false ∨ valuation q 1555 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1556 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1556)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 1 6 (meaning1518 q) (meaning1547 q) (meaning1556 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1547 = false ∨ valuation q 1556 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1552)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 2 1 (meaning1519 q) (meaning1542 q) (meaning1552 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1552 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1542 = false ∨ valuation q 1552 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1553)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 2 2 (meaning1519 q) (meaning1543 q) (meaning1553 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1543 = false ∨ valuation q 1553 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1554 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1554)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 2 3 (meaning1519 q) (meaning1544 q) (meaning1554 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1544 = false ∨ valuation q 1554 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1555 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1555)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 2 4 (meaning1519 q) (meaning1545 q) (meaning1555 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1545 = false ∨ valuation q 1555 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1556 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1556)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 2 5 (meaning1519 q) (meaning1546 q) (meaning1556 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1546 = false ∨ valuation q 1556 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1557)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 2 6 (meaning1519 q) (meaning1547 q) (meaning1557 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1547 = false ∨ valuation q 1557 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1553)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 3 1 (meaning1520 q) (meaning1542 q) (meaning1553 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1542 = false ∨ valuation q 1553 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1554)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 3 2 (meaning1520 q) (meaning1543 q) (meaning1554 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1543 = false ∨ valuation q 1554 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1555)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 3 3 (meaning1520 q) (meaning1544 q) (meaning1555 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1544 = false ∨ valuation q 1555 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1556 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1556)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 3 4 (meaning1520 q) (meaning1545 q) (meaning1556 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1545 = false ∨ valuation q 1556 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1557 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1557)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 3 5 (meaning1520 q) (meaning1546 q) (meaning1557 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1546 = false ∨ valuation q 1557 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1554)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 4 1 (meaning1521 q) (meaning1542 q) (meaning1554 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1542 = false ∨ valuation q 1554 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1555)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 4 2 (meaning1521 q) (meaning1543 q) (meaning1555 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1543 = false ∨ valuation q 1555 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1556 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1556)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 4 3 (meaning1521 q) (meaning1544 q) (meaning1556 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1544 = false ∨ valuation q 1556 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1557 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1557)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 4 4 (meaning1521 q) (meaning1545 q) (meaning1557 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1545 = false ∨ valuation q 1557 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1558 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -53, -54, -55, -56])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1558)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -53, -54, -55, -56]) (count1550 q) 4 5 (meaning1521 q) (meaning1546 q) (meaning1558 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1546 = false ∨ valuation q 1558 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E024.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112024
