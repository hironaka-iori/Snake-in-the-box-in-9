import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 1555 = true := by
  have hs : count1554 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_two (literal (valuation q) (-59)) (literal (valuation q) (-60)) (literal (valuation q) (1555)) (countLit q [-59]) (countLit q [-60]) (count1554 q) 1 1 (meaningNeg59 q) (meaningNeg60 q) (meaning1555 q) hs
  change (! (valuation q 59)) = false ∨ (! (valuation q 60)) = false ∨ valuation q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1556 = true := by
  have hs : count1556 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuation q) (1554)) (literal (valuation q) (1556)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1556 q) 1 (meaning1554 q) (meaning1556 q) hs
  change valuation q 1554 = false ∨ valuation q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1557 = true := by
  have hs : count1556 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuation q) (1555)) (literal (valuation q) (1557)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1556 q) 2 (meaning1555 q) (meaning1557 q) hs
  change valuation q 1555 = false ∨ valuation q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1556 = true := by
  have hs : count1556 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuation q) (1552)) (literal (valuation q) (1556)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1556 q) 1 (meaning1552 q) (meaning1556 q) hs
  change valuation q 1552 = false ∨ valuation q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1554 = false ∨ valuation q 1557 = true := by
  have hs : count1556 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuation q) (1552)) (literal (valuation q) (1554)) (literal (valuation q) (1557)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1556 q) 1 1 (meaning1552 q) (meaning1554 q) (meaning1557 q) hs
  change valuation q 1552 = false ∨ valuation q 1554 = false ∨ valuation q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1552 = false ∨ valuation q 1555 = false ∨ valuation q 1558 = true := by
  have hs : count1556 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuation q) (1552)) (literal (valuation q) (1555)) (literal (valuation q) (1558)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1556 q) 1 2 (meaning1552 q) (meaning1555 q) (meaning1558 q) hs
  change valuation q 1552 = false ∨ valuation q 1555 = false ∨ valuation q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1557 = true := by
  have hs : count1556 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuation q) (1553)) (literal (valuation q) (1557)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1556 q) 2 (meaning1553 q) (meaning1557 q) hs
  change valuation q 1553 = false ∨ valuation q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1554 = false ∨ valuation q 1558 = true := by
  have hs : count1556 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuation q) (1553)) (literal (valuation q) (1554)) (literal (valuation q) (1558)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1556 q) 2 1 (meaning1553 q) (meaning1554 q) (meaning1558 q) hs
  change valuation q 1553 = false ∨ valuation q 1554 = false ∨ valuation q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1555 = false ∨ valuation q 1559 = true := by
  have hs : count1556 q = (countLit q [-53, -56]) + (countLit q [-59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-53, -56]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuation q) (1553)) (literal (valuation q) (1555)) (literal (valuation q) (1559)) (countLit q [-53, -56]) (countLit q [-59, -60]) (count1556 q) 2 2 (meaning1553 q) (meaning1555 q) (meaning1559 q) hs
  change valuation q 1553 = false ∨ valuation q 1555 = false ∨ valuation q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_right (literal (valuation q) (1556)) (literal (valuation q) (1560)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 1 (meaning1556 q) (meaning1560 q) hs
  change valuation q 1556 = false ∨ valuation q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1561 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_right (literal (valuation q) (1557)) (literal (valuation q) (1561)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 2 (meaning1557 q) (meaning1561 q) hs
  change valuation q 1557 = false ∨ valuation q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1562 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_right (literal (valuation q) (1558)) (literal (valuation q) (1562)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 3 (meaning1558 q) (meaning1562 q) hs
  change valuation q 1558 = false ∨ valuation q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1563 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_right (literal (valuation q) (1559)) (literal (valuation q) (1563)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 4 (meaning1559 q) (meaning1563 q) hs
  change valuation q 1559 = false ∨ valuation q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1560 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_left (literal (valuation q) (1548)) (literal (valuation q) (1560)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 1 (meaning1548 q) (meaning1560 q) hs
  change valuation q 1548 = false ∨ valuation q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1556 = false ∨ valuation q 1561 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1548)) (literal (valuation q) (1556)) (literal (valuation q) (1561)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 1 1 (meaning1548 q) (meaning1556 q) (meaning1561 q) hs
  change valuation q 1548 = false ∨ valuation q 1556 = false ∨ valuation q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1557 = false ∨ valuation q 1562 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1548)) (literal (valuation q) (1557)) (literal (valuation q) (1562)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 1 2 (meaning1548 q) (meaning1557 q) (meaning1562 q) hs
  change valuation q 1548 = false ∨ valuation q 1557 = false ∨ valuation q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1558 = false ∨ valuation q 1563 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1548)) (literal (valuation q) (1558)) (literal (valuation q) (1563)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 1 3 (meaning1548 q) (meaning1558 q) (meaning1563 q) hs
  change valuation q 1548 = false ∨ valuation q 1558 = false ∨ valuation q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1559 = false ∨ valuation q 1564 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1548)) (literal (valuation q) (1559)) (literal (valuation q) (1564)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 1 4 (meaning1548 q) (meaning1559 q) (meaning1564 q) hs
  change valuation q 1548 = false ∨ valuation q 1559 = false ∨ valuation q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1561 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_left (literal (valuation q) (1549)) (literal (valuation q) (1561)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 2 (meaning1549 q) (meaning1561 q) hs
  change valuation q 1549 = false ∨ valuation q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1556 = false ∨ valuation q 1562 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1549)) (literal (valuation q) (1556)) (literal (valuation q) (1562)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 2 1 (meaning1549 q) (meaning1556 q) (meaning1562 q) hs
  change valuation q 1549 = false ∨ valuation q 1556 = false ∨ valuation q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1557 = false ∨ valuation q 1563 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1549)) (literal (valuation q) (1557)) (literal (valuation q) (1563)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 2 2 (meaning1549 q) (meaning1557 q) (meaning1563 q) hs
  change valuation q 1549 = false ∨ valuation q 1557 = false ∨ valuation q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1558 = false ∨ valuation q 1564 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1549)) (literal (valuation q) (1558)) (literal (valuation q) (1564)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 2 3 (meaning1549 q) (meaning1558 q) (meaning1564 q) hs
  change valuation q 1549 = false ∨ valuation q 1558 = false ∨ valuation q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1559 = false ∨ valuation q 1565 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1549)) (literal (valuation q) (1559)) (literal (valuation q) (1565)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 2 4 (meaning1549 q) (meaning1559 q) (meaning1565 q) hs
  change valuation q 1549 = false ∨ valuation q 1559 = false ∨ valuation q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1562 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_left (literal (valuation q) (1550)) (literal (valuation q) (1562)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 3 (meaning1550 q) (meaning1562 q) hs
  change valuation q 1550 = false ∨ valuation q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1556 = false ∨ valuation q 1563 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1550)) (literal (valuation q) (1556)) (literal (valuation q) (1563)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 3 1 (meaning1550 q) (meaning1556 q) (meaning1563 q) hs
  change valuation q 1550 = false ∨ valuation q 1556 = false ∨ valuation q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1557 = false ∨ valuation q 1564 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1550)) (literal (valuation q) (1557)) (literal (valuation q) (1564)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 3 2 (meaning1550 q) (meaning1557 q) (meaning1564 q) hs
  change valuation q 1550 = false ∨ valuation q 1557 = false ∨ valuation q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1558 = false ∨ valuation q 1565 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1550)) (literal (valuation q) (1558)) (literal (valuation q) (1565)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 3 3 (meaning1550 q) (meaning1558 q) (meaning1565 q) hs
  change valuation q 1550 = false ∨ valuation q 1558 = false ∨ valuation q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1550 = false ∨ valuation q 1559 = false ∨ valuation q 1566 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1550)) (literal (valuation q) (1559)) (literal (valuation q) (1566)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 3 4 (meaning1550 q) (meaning1559 q) (meaning1566 q) hs
  change valuation q 1550 = false ∨ valuation q 1559 = false ∨ valuation q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1556 = false ∨ valuation q 1564 = true := by
  have hs : count1560 q = (countLit q [-45, -47, -49, -50]) + (countLit q [-53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-45, -47, -49, -50]) (l₂ := [-53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1551)) (literal (valuation q) (1556)) (literal (valuation q) (1564)) (countLit q [-45, -47, -49, -50]) (countLit q [-53, -56, -59, -60]) (count1560 q) 4 1 (meaning1551 q) (meaning1556 q) (meaning1564 q) hs
  change valuation q 1551 = false ∨ valuation q 1556 = false ∨ valuation q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1571 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_right (literal (valuation q) (1563)) (literal (valuation q) (1571)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 4 (meaning1563 q) (meaning1571 q) hs
  change valuation q 1563 = false ∨ valuation q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1572 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_right (literal (valuation q) (1564)) (literal (valuation q) (1572)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 5 (meaning1564 q) (meaning1572 q) hs
  change valuation q 1564 = false ∨ valuation q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1574 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_right (literal (valuation q) (1566)) (literal (valuation q) (1574)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 7 (meaning1566 q) (meaning1574 q) hs
  change valuation q 1566 = false ∨ valuation q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block34 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.First112
