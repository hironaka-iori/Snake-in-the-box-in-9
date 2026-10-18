import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1558 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1558)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 2 2 (meaning1525 q) (meaning1548 q) (meaning1558 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1548 = false ∨ valuation q 1558 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1559 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1559)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 2 3 (meaning1525 q) (meaning1549 q) (meaning1559 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1549 = false ∨ valuation q 1559 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1560 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1560)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 2 4 (meaning1525 q) (meaning1550 q) (meaning1560 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1550 = false ∨ valuation q 1560 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1558 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1558)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 3 1 (meaning1526 q) (meaning1547 q) (meaning1558 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1547 = false ∨ valuation q 1558 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1559 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1559)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 3 2 (meaning1526 q) (meaning1548 q) (meaning1559 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1548 = false ∨ valuation q 1559 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1560 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1560)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 3 3 (meaning1526 q) (meaning1549 q) (meaning1560 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1549 = false ∨ valuation q 1560 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1560 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1560)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 4 2 (meaning1527 q) (meaning1548 q) (meaning1560 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1548 = false ∨ valuation q 1560 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1575 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1575)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 3 3 (meaning1499 q) (meaning1557 q) (meaning1575 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1557 = false ∨ valuation q 1575 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1576 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1576)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 3 4 (meaning1499 q) (meaning1558 q) (meaning1576 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1558 = false ∨ valuation q 1576 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1577 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1577)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 3 5 (meaning1499 q) (meaning1559 q) (meaning1577 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1559 = false ∨ valuation q 1577 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1578 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1578)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 3 6 (meaning1499 q) (meaning1560 q) (meaning1578 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1560 = false ∨ valuation q 1578 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1575 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1575)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 4 2 (meaning1500 q) (meaning1556 q) (meaning1575 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1556 = false ∨ valuation q 1575 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1576 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1576)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 4 3 (meaning1500 q) (meaning1557 q) (meaning1576 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1557 = false ∨ valuation q 1576 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1577 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1577)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 4 4 (meaning1500 q) (meaning1558 q) (meaning1577 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1558 = false ∨ valuation q 1577 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1578 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1578)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 4 5 (meaning1500 q) (meaning1559 q) (meaning1578 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1559 = false ∨ valuation q 1578 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1579 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1560)) (literal (valuationOf q) (1579)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 4 6 (meaning1500 q) (meaning1560 q) (meaning1579 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1560 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1560 = false ∨ valuation q 1579 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1577 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1577)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 5 3 (meaning1501 q) (meaning1557 q) (meaning1577 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1557 = false ∨ valuation q 1577 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1578 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1558)) (literal (valuationOf q) (1578)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 5 4 (meaning1501 q) (meaning1558 q) (meaning1578 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1558 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1558 = false ∨ valuation q 1578 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1578 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1557)) (literal (valuationOf q) (1578)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 6 3 (meaning1502 q) (meaning1557 q) (meaning1578 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1557 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1557 = false ∨ valuation q 1578 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1580 = true := by
  have hs : count1570 q = (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) + (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (l₂ := [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1559)) (literal (valuationOf q) (1580)) (countLit q [-3, -4, -6, -8, -11, -13, -14, -16, -20, -21, -22, -23, -27, -29]) (countLit q [-30, -33, -37, -38, -39, -40, -44, -46, -47, -48, -50, -53, -55, -56, -59]) (count1570 q) 6 5 (meaning1502 q) (meaning1559 q) (meaning1580 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1559 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1559 = false ∨ valuation q 1580 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_right (literal (valuationOf q) (-64)) (literal (valuationOf q) (1589)) (countLit q [-63]) (countLit q [-64]) (count1589 q) 1 (meaningNeg64 q) (meaning1589 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1589 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1589)) (countLit q [-63]) (countLit q [-64]) (count1589 q) 1 (meaningNeg63 q) (meaning1589 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1589 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 64 = true ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-63]) + (countLit q [-64]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-64)) (literal (valuationOf q) (1590)) (countLit q [-63]) (countLit q [-64]) (count1589 q) 1 1 (meaningNeg63 q) (meaningNeg64 q) (meaning1590 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 64)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 64 = true ∨ valuation q 1590 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1591)) (countLit q [-62]) (countLit q [-63, -64]) (count1591 q) 1 (meaning1589 q) (meaning1591 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1591 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1592)) (countLit q [-62]) (countLit q [-63, -64]) (count1591 q) 2 (meaning1590 q) (meaning1592 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1592 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (1591)) (countLit q [-62]) (countLit q [-63, -64]) (count1591 q) 1 (meaningNeg62 q) (meaning1591 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1591 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1592)) (countLit q [-62]) (countLit q [-63, -64]) (count1591 q) 1 1 (meaningNeg62 q) (meaning1589 q) (meaning1592 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1589 = false ∨ valuation q 1592 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-62]) + (countLit q [-63, -64]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -64])
  have hm := merge_two (literal (valuationOf q) (-62)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1593)) (countLit q [-62]) (countLit q [-63, -64]) (count1591 q) 1 2 (meaningNeg62 q) (meaning1590 q) (meaning1593 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1590 = false ∨ valuation q 1593 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_right (literal (valuationOf q) (-67)) (literal (valuationOf q) (1594)) (countLit q [-65]) (countLit q [-67]) (count1594 q) 1 (meaningNeg67 q) (meaning1594 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1594 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1594)) (countLit q [-65]) (countLit q [-67]) (count1594 q) 1 (meaningNeg65 q) (meaning1594 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1594 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 67 = true ∨ valuationOf q 1595 = true := by
  have hs : count1594 q = (countLit q [-65]) + (countLit q [-67]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-67)) (literal (valuationOf q) (1595)) (countLit q [-65]) (countLit q [-67]) (count1594 q) 1 1 (meaningNeg65 q) (meaningNeg67 q) (meaning1595 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 67)) = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 67 = true ∨ valuation q 1595 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-70]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1596)) (countLit q [-70]) (countLit q [-73]) (count1596 q) 1 (meaningNeg70 q) (meaning1596 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1596 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E152.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112152
