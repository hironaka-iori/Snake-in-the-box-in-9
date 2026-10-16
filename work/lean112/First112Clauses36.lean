import First112Semantics
import Dfs112FirstBooleanInputs
namespace Snake9.Regrowth.First112
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1574 = false ∨ valuation q 1593 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1507)) (literal (valuation q) (1574)) (literal (valuation q) (1593)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 3 7 (meaning1507 q) (meaning1574 q) (meaning1593 q) hs
  change valuation q 1507 = false ∨ valuation q 1574 = false ∨ valuation q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1575 = false ∨ valuation q 1594 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1507)) (literal (valuation q) (1575)) (literal (valuation q) (1594)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 3 8 (meaning1507 q) (meaning1575 q) (meaning1594 q) hs
  change valuation q 1507 = false ∨ valuation q 1575 = false ∨ valuation q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1576 = false ∨ valuation q 1595 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1507)) (literal (valuation q) (1576)) (literal (valuation q) (1595)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 3 9 (meaning1507 q) (meaning1576 q) (meaning1595 q) hs
  change valuation q 1507 = false ∨ valuation q 1576 = false ∨ valuation q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1570 = false ∨ valuation q 1590 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1508)) (literal (valuation q) (1570)) (literal (valuation q) (1590)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 4 3 (meaning1508 q) (meaning1570 q) (meaning1590 q) hs
  change valuation q 1508 = false ∨ valuation q 1570 = false ∨ valuation q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1571 = false ∨ valuation q 1591 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1508)) (literal (valuation q) (1571)) (literal (valuation q) (1591)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 4 4 (meaning1508 q) (meaning1571 q) (meaning1591 q) hs
  change valuation q 1508 = false ∨ valuation q 1571 = false ∨ valuation q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1572 = false ∨ valuation q 1592 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1508)) (literal (valuation q) (1572)) (literal (valuation q) (1592)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 4 5 (meaning1508 q) (meaning1572 q) (meaning1592 q) hs
  change valuation q 1508 = false ∨ valuation q 1572 = false ∨ valuation q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1573 = false ∨ valuation q 1593 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1508)) (literal (valuation q) (1573)) (literal (valuation q) (1593)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 4 6 (meaning1508 q) (meaning1573 q) (meaning1593 q) hs
  change valuation q 1508 = false ∨ valuation q 1573 = false ∨ valuation q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1574 = false ∨ valuation q 1594 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1508)) (literal (valuation q) (1574)) (literal (valuation q) (1594)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 4 7 (meaning1508 q) (meaning1574 q) (meaning1594 q) hs
  change valuation q 1508 = false ∨ valuation q 1574 = false ∨ valuation q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1575 = false ∨ valuation q 1595 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1508)) (literal (valuation q) (1575)) (literal (valuation q) (1595)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 4 8 (meaning1508 q) (meaning1575 q) (meaning1595 q) hs
  change valuation q 1508 = false ∨ valuation q 1575 = false ∨ valuation q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1576 = false ∨ valuation q 1596 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1508)) (literal (valuation q) (1576)) (literal (valuation q) (1596)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 4 9 (meaning1508 q) (meaning1576 q) (meaning1596 q) hs
  change valuation q 1508 = false ∨ valuation q 1576 = false ∨ valuation q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1577 = false ∨ valuation q 1597 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1508)) (literal (valuation q) (1577)) (literal (valuation q) (1597)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 4 10 (meaning1508 q) (meaning1577 q) (meaning1597 q) hs
  change valuation q 1508 = false ∨ valuation q 1577 = false ∨ valuation q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1570 = false ∨ valuation q 1591 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1509)) (literal (valuation q) (1570)) (literal (valuation q) (1591)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 5 3 (meaning1509 q) (meaning1570 q) (meaning1591 q) hs
  change valuation q 1509 = false ∨ valuation q 1570 = false ∨ valuation q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1571 = false ∨ valuation q 1592 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1509)) (literal (valuation q) (1571)) (literal (valuation q) (1592)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 5 4 (meaning1509 q) (meaning1571 q) (meaning1592 q) hs
  change valuation q 1509 = false ∨ valuation q 1571 = false ∨ valuation q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1572 = false ∨ valuation q 1593 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1509)) (literal (valuation q) (1572)) (literal (valuation q) (1593)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 5 5 (meaning1509 q) (meaning1572 q) (meaning1593 q) hs
  change valuation q 1509 = false ∨ valuation q 1572 = false ∨ valuation q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1573 = false ∨ valuation q 1594 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1509)) (literal (valuation q) (1573)) (literal (valuation q) (1594)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 5 6 (meaning1509 q) (meaning1573 q) (meaning1594 q) hs
  change valuation q 1509 = false ∨ valuation q 1573 = false ∨ valuation q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1574 = false ∨ valuation q 1595 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1509)) (literal (valuation q) (1574)) (literal (valuation q) (1595)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 5 7 (meaning1509 q) (meaning1574 q) (meaning1595 q) hs
  change valuation q 1509 = false ∨ valuation q 1574 = false ∨ valuation q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1575 = false ∨ valuation q 1596 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1509)) (literal (valuation q) (1575)) (literal (valuation q) (1596)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 5 8 (meaning1509 q) (meaning1575 q) (meaning1596 q) hs
  change valuation q 1509 = false ∨ valuation q 1575 = false ∨ valuation q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1576 = false ∨ valuation q 1597 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1509)) (literal (valuation q) (1576)) (literal (valuation q) (1597)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 5 9 (meaning1509 q) (meaning1576 q) (meaning1597 q) hs
  change valuation q 1509 = false ∨ valuation q 1576 = false ∨ valuation q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1570 = false ∨ valuation q 1592 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1510)) (literal (valuation q) (1570)) (literal (valuation q) (1592)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 6 3 (meaning1510 q) (meaning1570 q) (meaning1592 q) hs
  change valuation q 1510 = false ∨ valuation q 1570 = false ∨ valuation q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1571 = false ∨ valuation q 1593 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1510)) (literal (valuation q) (1571)) (literal (valuation q) (1593)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 6 4 (meaning1510 q) (meaning1571 q) (meaning1593 q) hs
  change valuation q 1510 = false ∨ valuation q 1571 = false ∨ valuation q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1572 = false ∨ valuation q 1594 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1510)) (literal (valuation q) (1572)) (literal (valuation q) (1594)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 6 5 (meaning1510 q) (meaning1572 q) (meaning1594 q) hs
  change valuation q 1510 = false ∨ valuation q 1572 = false ∨ valuation q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1573 = false ∨ valuation q 1595 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1510)) (literal (valuation q) (1573)) (literal (valuation q) (1595)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 6 6 (meaning1510 q) (meaning1573 q) (meaning1595 q) hs
  change valuation q 1510 = false ∨ valuation q 1573 = false ∨ valuation q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1574 = false ∨ valuation q 1596 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1510)) (literal (valuation q) (1574)) (literal (valuation q) (1596)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 6 7 (meaning1510 q) (meaning1574 q) (meaning1596 q) hs
  change valuation q 1510 = false ∨ valuation q 1574 = false ∨ valuation q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1570 = false ∨ valuation q 1593 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1511)) (literal (valuation q) (1570)) (literal (valuation q) (1593)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 7 3 (meaning1511 q) (meaning1570 q) (meaning1593 q) hs
  change valuation q 1511 = false ∨ valuation q 1570 = false ∨ valuation q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1571 = false ∨ valuation q 1594 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1511)) (literal (valuation q) (1571)) (literal (valuation q) (1594)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 7 4 (meaning1511 q) (meaning1571 q) (meaning1594 q) hs
  change valuation q 1511 = false ∨ valuation q 1571 = false ∨ valuation q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1572 = false ∨ valuation q 1595 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1511)) (literal (valuation q) (1572)) (literal (valuation q) (1595)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 7 5 (meaning1511 q) (meaning1572 q) (meaning1595 q) hs
  change valuation q 1511 = false ∨ valuation q 1572 = false ∨ valuation q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1573 = false ∨ valuation q 1596 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1511)) (literal (valuation q) (1573)) (literal (valuation q) (1596)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 7 6 (meaning1511 q) (meaning1573 q) (meaning1596 q) hs
  change valuation q 1511 = false ∨ valuation q 1573 = false ∨ valuation q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1574 = false ∨ valuation q 1597 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1511)) (literal (valuation q) (1574)) (literal (valuation q) (1597)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 7 7 (meaning1511 q) (meaning1574 q) (meaning1597 q) hs
  change valuation q 1511 = false ∨ valuation q 1574 = false ∨ valuation q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1570 = false ∨ valuation q 1594 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1512)) (literal (valuation q) (1570)) (literal (valuation q) (1594)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 8 3 (meaning1512 q) (meaning1570 q) (meaning1594 q) hs
  change valuation q 1512 = false ∨ valuation q 1570 = false ∨ valuation q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1571 = false ∨ valuation q 1595 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1512)) (literal (valuation q) (1571)) (literal (valuation q) (1595)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 8 4 (meaning1512 q) (meaning1571 q) (meaning1595 q) hs
  change valuation q 1512 = false ∨ valuation q 1571 = false ∨ valuation q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1572 = false ∨ valuation q 1596 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1512)) (literal (valuation q) (1572)) (literal (valuation q) (1596)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 8 5 (meaning1512 q) (meaning1572 q) (meaning1596 q) hs
  change valuation q 1512 = false ∨ valuation q 1572 = false ∨ valuation q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1573 = false ∨ valuation q 1597 = true := by
  have hs : count1584 q = (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) + (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) := List.countP_append (p := literal (baseVal q)) (l₁ := [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (l₂ := [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60])
  have hm := merge_two (literal (valuation q) (1512)) (literal (valuation q) (1573)) (literal (valuation q) (1597)) (countLit q [-2, -4, -6, -8, -10, -12, -13, -15, -18, -19, -21, -23, -24, -26, -27]) (countLit q [-31, -33, -34, -35, -39, -41, -42, -43, -45, -47, -49, -50, -53, -56, -59, -60]) (count1584 q) 8 6 (meaning1512 q) (meaning1573 q) (meaning1597 q) hs
  change valuation q 1512 = false ∨ valuation q 1573 = false ∨ valuation q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem block36 (q : Snake 81) (h : Conditions q) : Dfs112FirstBoolean.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.First112
