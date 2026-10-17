import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 3 5 (meaning1487 q) (meaning1543 q) (meaning1560 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1543 = false ∨ valuation q 1560 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 3 6 (meaning1487 q) (meaning1544 q) (meaning1561 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1544 = false ∨ valuation q 1561 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1562 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1562)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 3 7 (meaning1487 q) (meaning1545 q) (meaning1562 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1545 = false ∨ valuation q 1562 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 4 2 (meaning1488 q) (meaning1540 q) (meaning1558 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1540 = false ∨ valuation q 1558 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 4 3 (meaning1488 q) (meaning1541 q) (meaning1559 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1541 = false ∨ valuation q 1559 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 4 4 (meaning1488 q) (meaning1542 q) (meaning1560 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1542 = false ∨ valuation q 1560 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 4 5 (meaning1488 q) (meaning1543 q) (meaning1561 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1543 = false ∨ valuation q 1561 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1562 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1562)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 4 6 (meaning1488 q) (meaning1544 q) (meaning1562 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1544 = false ∨ valuation q 1562 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1563 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1563)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 4 7 (meaning1488 q) (meaning1545 q) (meaning1563 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1545 = false ∨ valuation q 1563 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 5 2 (meaning1489 q) (meaning1540 q) (meaning1559 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1540 = false ∨ valuation q 1559 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 5 3 (meaning1489 q) (meaning1541 q) (meaning1560 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1541 = false ∨ valuation q 1560 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 5 4 (meaning1489 q) (meaning1542 q) (meaning1561 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1542 = false ∨ valuation q 1561 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1562 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1562)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 5 5 (meaning1489 q) (meaning1543 q) (meaning1562 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1543 = false ∨ valuation q 1562 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 6 3 (meaning1490 q) (meaning1541 q) (meaning1561 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1541 = false ∨ valuation q 1561 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1562 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1562)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 6 4 (meaning1490 q) (meaning1542 q) (meaning1562 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1542 = false ∨ valuation q 1562 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1563 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1563)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 6 5 (meaning1490 q) (meaning1543 q) (meaning1563 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1543 = false ∨ valuation q 1563 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_right (literal (valuationOf q) (-65)) (literal (valuationOf q) (1569)) (countLit q [-64]) (countLit q [-65]) (count1569 q) 1 (meaningNeg65 q) (meaning1569 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1569 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1569)) (countLit q [-64]) (countLit q [-65]) (count1569 q) 1 (meaningNeg64 q) (meaning1569 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1569 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 65 = true ∨ valuationOf q 1570 = true := by
  have hs : count1569 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-65)) (literal (valuationOf q) (1570)) (countLit q [-64]) (countLit q [-65]) (count1569 q) 1 1 (meaningNeg64 q) (meaningNeg65 q) (meaning1570 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 65)) = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 65 = true ∨ valuation q 1570 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-61]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64, -65])
  have hm := merge_right (literal (valuationOf q) (1569)) (literal (valuationOf q) (1571)) (countLit q [-61]) (countLit q [-64, -65]) (count1571 q) 1 (meaning1569 q) (meaning1571 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1571 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-61]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64, -65])
  have hm := merge_right (literal (valuationOf q) (1570)) (literal (valuationOf q) (1572)) (countLit q [-61]) (countLit q [-64, -65]) (count1571 q) 2 (meaning1570 q) (meaning1572 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1572 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (1574)) (countLit q [-67]) (countLit q [-68]) (count1574 q) 1 (meaningNeg68 q) (meaning1574 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1574 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1574)) (countLit q [-67]) (countLit q [-68]) (count1574 q) 1 (meaningNeg67 q) (meaning1574 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1574 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 68 = true ∨ valuationOf q 1575 = true := by
  have hs : count1574 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (1575)) (countLit q [-67]) (countLit q [-68]) (count1574 q) 1 1 (meaningNeg67 q) (meaningNeg68 q) (meaning1575 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 1575 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1576)) (countLit q [-72]) (countLit q [-74]) (count1576 q) 1 (meaningNeg74 q) (meaning1576 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1576 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1576)) (countLit q [-72]) (countLit q [-74]) (count1576 q) 1 (meaningNeg72 q) (meaning1576 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1576 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1577)) (countLit q [-72]) (countLit q [-74]) (count1576 q) 1 1 (meaningNeg72 q) (meaningNeg74 q) (meaning1577 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 74 = true ∨ valuation q 1577 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-67, -68]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (1576)) (literal (valuationOf q) (1578)) (countLit q [-67, -68]) (countLit q [-72, -74]) (count1578 q) 1 (meaning1576 q) (meaning1578 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1578 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-67, -68]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (1577)) (literal (valuationOf q) (1579)) (countLit q [-67, -68]) (countLit q [-72, -74]) (count1578 q) 2 (meaning1577 q) (meaning1579 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1579 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-67, -68]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-72, -74])
  have hm := merge_left (literal (valuationOf q) (1574)) (literal (valuationOf q) (1578)) (countLit q [-67, -68]) (countLit q [-72, -74]) (count1578 q) 1 (meaning1574 q) (meaning1578 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1578 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-67, -68]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1579)) (countLit q [-67, -68]) (countLit q [-72, -74]) (count1578 q) 1 1 (meaning1574 q) (meaning1576 q) (meaning1579 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1576 = false ∨ valuation q 1579 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true := by
  have hs : count1578 q = (countLit q [-67, -68]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1580)) (countLit q [-67, -68]) (countLit q [-72, -74]) (count1578 q) 1 2 (meaning1574 q) (meaning1577 q) (meaning1580 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1577 = false ∨ valuation q 1580 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E007.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112007
