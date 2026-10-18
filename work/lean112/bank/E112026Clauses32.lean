import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1557)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 2 6 (meaning1519 q) (meaning1547 q) (meaning1557 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1547 = false ∨ valuation q 1557 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1553)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 3 1 (meaning1520 q) (meaning1542 q) (meaning1553 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1542 = false ∨ valuation q 1553 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1554)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 3 2 (meaning1520 q) (meaning1543 q) (meaning1554 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1543 = false ∨ valuation q 1554 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1555)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 3 3 (meaning1520 q) (meaning1544 q) (meaning1555 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1544 = false ∨ valuation q 1555 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1556 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1556)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 3 4 (meaning1520 q) (meaning1545 q) (meaning1556 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1545 = false ∨ valuation q 1556 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1557 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1557)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 3 5 (meaning1520 q) (meaning1546 q) (meaning1557 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1546 = false ∨ valuation q 1557 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1558 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1558)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 3 6 (meaning1520 q) (meaning1547 q) (meaning1558 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1547 = false ∨ valuation q 1558 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1554)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 4 1 (meaning1521 q) (meaning1542 q) (meaning1554 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1542 = false ∨ valuation q 1554 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1555)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 4 2 (meaning1521 q) (meaning1543 q) (meaning1555 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1543 = false ∨ valuation q 1555 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1556 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1556)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 4 3 (meaning1521 q) (meaning1544 q) (meaning1556 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1544 = false ∨ valuation q 1556 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1557 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1557)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 4 4 (meaning1521 q) (meaning1545 q) (meaning1557 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1545 = false ∨ valuation q 1557 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1556 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1556)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 5 2 (meaning1522 q) (meaning1543 q) (meaning1556 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1543 = false ∨ valuation q 1556 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1557 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1557)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 5 3 (meaning1522 q) (meaning1544 q) (meaning1557 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1544 = false ∨ valuation q 1557 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1558 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1558)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 5 4 (meaning1522 q) (meaning1545 q) (meaning1558 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1545 = false ∨ valuation q 1558 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1559 = true := by
  have hs : count1550 q = (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) + (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-28, -31, -33, -35, -36, -37, -39, -41]) (l₂ := [-43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1559)) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41]) (countLit q [-43, -44, -47, -50, -52, -53, -54, -55]) (count1550 q) 5 5 (meaning1522 q) (meaning1546 q) (meaning1559 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1546 = false ∨ valuation q 1559 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 3 7 (meaning1489 q) (meaning1556 q) (meaning1575 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1556 = false ∨ valuation q 1575 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1573)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 4 4 (meaning1490 q) (meaning1553 q) (meaning1573 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1553 = false ∨ valuation q 1573 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1574 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1574)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 4 5 (meaning1490 q) (meaning1554 q) (meaning1574 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1554 = false ∨ valuation q 1574 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 4 6 (meaning1490 q) (meaning1555 q) (meaning1575 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1555 = false ∨ valuation q 1575 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1576 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1576)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 4 7 (meaning1490 q) (meaning1556 q) (meaning1576 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1556 = false ∨ valuation q 1576 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1577 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1577)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 4 8 (meaning1490 q) (meaning1557 q) (meaning1577 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1557 = false ∨ valuation q 1577 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1578 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1578)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 4 9 (meaning1490 q) (meaning1558 q) (meaning1578 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1558 = false ∨ valuation q 1578 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1573)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 5 3 (meaning1491 q) (meaning1552 q) (meaning1573 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1552 = false ∨ valuation q 1573 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1574 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1574)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 5 4 (meaning1491 q) (meaning1553 q) (meaning1574 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1553 = false ∨ valuation q 1574 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1554)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 5 5 (meaning1491 q) (meaning1554 q) (meaning1575 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1554 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1554 = false ∨ valuation q 1575 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1576 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1576)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 5 6 (meaning1491 q) (meaning1555 q) (meaning1576 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1555 = false ∨ valuation q 1576 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1577 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1577)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 5 7 (meaning1491 q) (meaning1556 q) (meaning1577 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1556 = false ∨ valuation q 1577 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1578 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1578)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 5 8 (meaning1491 q) (meaning1557 q) (meaning1578 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1557 = false ∨ valuation q 1578 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1579 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1579)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 5 9 (meaning1491 q) (meaning1558 q) (meaning1579 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1558 = false ∨ valuation q 1579 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1580 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1580)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 5 10 (meaning1491 q) (meaning1559 q) (meaning1580 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1559 = false ∨ valuation q 1580 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1574 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1552)) (literal (valuationOf q) (1574)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 6 3 (meaning1492 q) (meaning1552 q) (meaning1574 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1552 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1552 = false ∨ valuation q 1574 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1575 = true := by
  have hs : count1566 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) + (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (l₂ := [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26]) (countLit q [-28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (count1566 q) 6 4 (meaning1492 q) (meaning1553 q) (meaning1575 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1553 = false ∨ valuation q 1575 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E026.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112026
