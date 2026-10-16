import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1561 = false ∨ valuation q 1570 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1536)) (literal (valuation q) (1561)) (literal (valuation q) (1570)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 1 2 (meaning1536 q) (meaning1561 q) (meaning1570 q) hs
  change valuation q 1536 = false ∨ valuation q 1561 = false ∨ valuation q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1562 = false ∨ valuation q 1571 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1536)) (literal (valuation q) (1562)) (literal (valuation q) (1571)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 1 3 (meaning1536 q) (meaning1562 q) (meaning1571 q) hs
  change valuation q 1536 = false ∨ valuation q 1562 = false ∨ valuation q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1563 = false ∨ valuation q 1572 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1536)) (literal (valuation q) (1563)) (literal (valuation q) (1572)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 1 4 (meaning1536 q) (meaning1563 q) (meaning1572 q) hs
  change valuation q 1536 = false ∨ valuation q 1563 = false ∨ valuation q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1564 = false ∨ valuation q 1573 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1536)) (literal (valuation q) (1564)) (literal (valuation q) (1573)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 1 5 (meaning1536 q) (meaning1564 q) (meaning1573 q) hs
  change valuation q 1536 = false ∨ valuation q 1564 = false ∨ valuation q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1565 = false ∨ valuation q 1574 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1536)) (literal (valuation q) (1565)) (literal (valuation q) (1574)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 1 6 (meaning1536 q) (meaning1565 q) (meaning1574 q) hs
  change valuation q 1536 = false ∨ valuation q 1565 = false ∨ valuation q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1560 = false ∨ valuation q 1570 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1537)) (literal (valuation q) (1560)) (literal (valuation q) (1570)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 2 1 (meaning1537 q) (meaning1560 q) (meaning1570 q) hs
  change valuation q 1537 = false ∨ valuation q 1560 = false ∨ valuation q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1561 = false ∨ valuation q 1571 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1537)) (literal (valuation q) (1561)) (literal (valuation q) (1571)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 2 2 (meaning1537 q) (meaning1561 q) (meaning1571 q) hs
  change valuation q 1537 = false ∨ valuation q 1561 = false ∨ valuation q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1562 = false ∨ valuation q 1572 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1537)) (literal (valuation q) (1562)) (literal (valuation q) (1572)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 2 3 (meaning1537 q) (meaning1562 q) (meaning1572 q) hs
  change valuation q 1537 = false ∨ valuation q 1562 = false ∨ valuation q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1563 = false ∨ valuation q 1573 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1537)) (literal (valuation q) (1563)) (literal (valuation q) (1573)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 2 4 (meaning1537 q) (meaning1563 q) (meaning1573 q) hs
  change valuation q 1537 = false ∨ valuation q 1563 = false ∨ valuation q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1564 = false ∨ valuation q 1574 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1537)) (literal (valuation q) (1564)) (literal (valuation q) (1574)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 2 5 (meaning1537 q) (meaning1564 q) (meaning1574 q) hs
  change valuation q 1537 = false ∨ valuation q 1564 = false ∨ valuation q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1565 = false ∨ valuation q 1575 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1537)) (literal (valuation q) (1565)) (literal (valuation q) (1575)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 2 6 (meaning1537 q) (meaning1565 q) (meaning1575 q) hs
  change valuation q 1537 = false ∨ valuation q 1565 = false ∨ valuation q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1570 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_left (literal (valuation q) (1538)) (literal (valuation q) (1570)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 3 (meaning1538 q) (meaning1570 q) hs
  change valuation q 1538 = false ∨ valuation q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1560 = false ∨ valuation q 1571 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1538)) (literal (valuation q) (1560)) (literal (valuation q) (1571)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 3 1 (meaning1538 q) (meaning1560 q) (meaning1571 q) hs
  change valuation q 1538 = false ∨ valuation q 1560 = false ∨ valuation q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1561 = false ∨ valuation q 1572 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1538)) (literal (valuation q) (1561)) (literal (valuation q) (1572)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 3 2 (meaning1538 q) (meaning1561 q) (meaning1572 q) hs
  change valuation q 1538 = false ∨ valuation q 1561 = false ∨ valuation q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1562 = false ∨ valuation q 1573 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1538)) (literal (valuation q) (1562)) (literal (valuation q) (1573)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 3 3 (meaning1538 q) (meaning1562 q) (meaning1573 q) hs
  change valuation q 1538 = false ∨ valuation q 1562 = false ∨ valuation q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1563 = false ∨ valuation q 1574 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1538)) (literal (valuation q) (1563)) (literal (valuation q) (1574)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 3 4 (meaning1538 q) (meaning1563 q) (meaning1574 q) hs
  change valuation q 1538 = false ∨ valuation q 1563 = false ∨ valuation q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1564 = false ∨ valuation q 1575 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1538)) (literal (valuation q) (1564)) (literal (valuation q) (1575)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 3 5 (meaning1538 q) (meaning1564 q) (meaning1575 q) hs
  change valuation q 1538 = false ∨ valuation q 1564 = false ∨ valuation q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1571 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_left (literal (valuation q) (1539)) (literal (valuation q) (1571)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 4 (meaning1539 q) (meaning1571 q) hs
  change valuation q 1539 = false ∨ valuation q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1560 = false ∨ valuation q 1572 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1539)) (literal (valuation q) (1560)) (literal (valuation q) (1572)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 4 1 (meaning1539 q) (meaning1560 q) (meaning1572 q) hs
  change valuation q 1539 = false ∨ valuation q 1560 = false ∨ valuation q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1561 = false ∨ valuation q 1573 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1539)) (literal (valuation q) (1561)) (literal (valuation q) (1573)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 4 2 (meaning1539 q) (meaning1561 q) (meaning1573 q) hs
  change valuation q 1539 = false ∨ valuation q 1561 = false ∨ valuation q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1562 = false ∨ valuation q 1574 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1539)) (literal (valuation q) (1562)) (literal (valuation q) (1574)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 4 3 (meaning1539 q) (meaning1562 q) (meaning1574 q) hs
  change valuation q 1539 = false ∨ valuation q 1562 = false ∨ valuation q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1563 = false ∨ valuation q 1575 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1539)) (literal (valuation q) (1563)) (literal (valuation q) (1575)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 4 4 (meaning1539 q) (meaning1563 q) (meaning1575 q) hs
  change valuation q 1539 = false ∨ valuation q 1563 = false ∨ valuation q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1564 = false ∨ valuation q 1576 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1539)) (literal (valuation q) (1564)) (literal (valuation q) (1576)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 4 5 (meaning1539 q) (meaning1564 q) (meaning1576 q) hs
  change valuation q 1539 = false ∨ valuation q 1564 = false ∨ valuation q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1565 = false ∨ valuation q 1577 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1539)) (literal (valuation q) (1565)) (literal (valuation q) (1577)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 4 6 (meaning1539 q) (meaning1565 q) (meaning1577 q) hs
  change valuation q 1539 = false ∨ valuation q 1565 = false ∨ valuation q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1572 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_left (literal (valuation q) (1540)) (literal (valuation q) (1572)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 5 (meaning1540 q) (meaning1572 q) hs
  change valuation q 1540 = false ∨ valuation q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1560 = false ∨ valuation q 1573 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1540)) (literal (valuation q) (1560)) (literal (valuation q) (1573)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 5 1 (meaning1540 q) (meaning1560 q) (meaning1573 q) hs
  change valuation q 1540 = false ∨ valuation q 1560 = false ∨ valuation q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1561 = false ∨ valuation q 1574 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1540)) (literal (valuation q) (1561)) (literal (valuation q) (1574)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 5 2 (meaning1540 q) (meaning1561 q) (meaning1574 q) hs
  change valuation q 1540 = false ∨ valuation q 1561 = false ∨ valuation q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1562 = false ∨ valuation q 1575 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1540)) (literal (valuation q) (1562)) (literal (valuation q) (1575)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 5 3 (meaning1540 q) (meaning1562 q) (meaning1575 q) hs
  change valuation q 1540 = false ∨ valuation q 1562 = false ∨ valuation q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1563 = false ∨ valuation q 1576 = true := by
  have hs : count1568 q = (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) + (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-31, -33, -34, -35, -39, -41, -42, -43]) (l₂ := [-45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1540)) (literal (valuation q) (1563)) (literal (valuation q) (1576)) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43]) (countLit q [-45, -47, -49, -50, -53, -56, -59, -60]) (count1568 q) 5 4 (meaning1540 q) (meaning1563 q) (meaning1576 q) hs
  change valuation q 1540 = false ∨ valuation q 1563 = false ∨ valuation q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1571 = false ∨ valuation q 1590 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1507)) (literal (valuation q) (1571)) (literal (valuation q) (1590)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 3 4 (meaning1507 q) (meaning1571 q) (meaning1590 q) hs
  change valuation q 1507 = false ∨ valuation q 1571 = false ∨ valuation q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1572 = false ∨ valuation q 1591 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1507)) (literal (valuation q) (1572)) (literal (valuation q) (1591)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 3 5 (meaning1507 q) (meaning1572 q) (meaning1591 q) hs
  change valuation q 1507 = false ∨ valuation q 1572 = false ∨ valuation q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1573 = false ∨ valuation q 1592 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1507)) (literal (valuation q) (1573)) (literal (valuation q) (1592)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 3 6 (meaning1507 q) (meaning1573 q) (meaning1592 q) hs
  change valuation q 1507 = false ∨ valuation q 1573 = false ∨ valuation q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block35 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.First112
