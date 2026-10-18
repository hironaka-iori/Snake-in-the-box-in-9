import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1575 = true := by
  have hs : count1570 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1575)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1570 q) 2 4 (meaning1559 q) (meaning1569 q) (meaning1575 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1569 = false ∨ valuation q 1575 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1574 = true := by
  have hs : count1570 q = (countLit q [-1, -3, -5, -7]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -7]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1567)) (literal (valuationOf q) (1574)) (countLit q [-1, -3, -5, -7]) (countLit q [-8, -10, -11, -12]) (count1570 q) 3 2 (meaning1560 q) (meaning1567 q) (meaning1574 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1567 = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1567 = false ∨ valuation q 1574 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-13]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-16])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1578)) (countLit q [-13]) (countLit q [-16]) (count1578 q) 1 (meaningNeg13 q) (meaning1578 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1578 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 16 = true ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-13]) + (countLit q [-16]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-16])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-16)) (literal (valuationOf q) (1579)) (countLit q [-13]) (countLit q [-16]) (count1578 q) 1 1 (meaningNeg13 q) (meaningNeg16 q) (meaning1579 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 16)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 16 = true ∨ valuation q 1579 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1580)) (countLit q [-18]) (countLit q [-19]) (count1580 q) 1 (meaningNeg19 q) (meaning1580 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1580 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1580)) (countLit q [-18]) (countLit q [-19]) (count1580 q) 1 (meaningNeg18 q) (meaning1580 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1580 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1581)) (countLit q [-18]) (countLit q [-19]) (count1580 q) 1 1 (meaningNeg18 q) (meaningNeg19 q) (meaning1581 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 1581 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-13, -16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -16]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (countLit q [-13, -16]) (countLit q [-18, -19]) (count1582 q) 2 (meaning1581 q) (meaning1583 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-13, -16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -16]) (l₂ := [-18, -19])
  have hm := merge_left (literal (valuationOf q) (1578)) (literal (valuationOf q) (1582)) (countLit q [-13, -16]) (countLit q [-18, -19]) (count1582 q) 1 (meaning1578 q) (meaning1582 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1582 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-13, -16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -16]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1583)) (countLit q [-13, -16]) (countLit q [-18, -19]) (count1582 q) 1 1 (meaning1578 q) (meaning1580 q) (meaning1583 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = false ∨ valuation q 1583 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-13, -16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -16]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-13, -16]) (countLit q [-18, -19]) (count1582 q) 1 2 (meaning1578 q) (meaning1581 q) (meaning1584 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-13, -16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -16]) (l₂ := [-18, -19])
  have hm := merge_left (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-13, -16]) (countLit q [-18, -19]) (count1582 q) 2 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-13, -16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -16]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-13, -16]) (countLit q [-18, -19]) (count1582 q) 2 1 (meaning1579 q) (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1580 = false ∨ valuation q 1584 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-13, -16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-13, -16]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-13, -16]) (countLit q [-18, -19]) (count1582 q) 2 2 (meaning1579 q) (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1586 = true := by
  have hs : count1586 q = (countLit q [-21]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1586)) (countLit q [-21]) (countLit q [-25]) (count1586 q) 1 (meaningNeg25 q) (meaning1586 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1586 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1586 = true := by
  have hs : count1586 q = (countLit q [-21]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1586)) (countLit q [-21]) (countLit q [-25]) (count1586 q) 1 (meaningNeg21 q) (meaning1586 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1586 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1587 = true := by
  have hs : count1586 q = (countLit q [-21]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1587)) (countLit q [-21]) (countLit q [-25]) (count1586 q) 1 1 (meaningNeg21 q) (meaningNeg25 q) (meaning1587 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 25 = true ∨ valuation q 1587 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1588 = true := by
  have hs : count1588 q = (countLit q [-27]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28])
  have hm := merge_right (literal (valuationOf q) (-28)) (literal (valuationOf q) (1588)) (countLit q [-27]) (countLit q [-28]) (count1588 q) 1 (meaningNeg28 q) (meaning1588 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1588 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1588 = true := by
  have hs : count1588 q = (countLit q [-27]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1588)) (countLit q [-27]) (countLit q [-28]) (count1588 q) 1 (meaningNeg27 q) (meaning1588 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1588 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 28 = true ∨ valuationOf q 1589 = true := by
  have hs : count1588 q = (countLit q [-27]) + (countLit q [-28]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-28)) (literal (valuationOf q) (1589)) (countLit q [-27]) (countLit q [-28]) (count1588 q) 1 1 (meaningNeg27 q) (meaningNeg28 q) (meaning1589 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 28)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 28 = true ∨ valuation q 1589 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1590 = true := by
  have hs : count1590 q = (countLit q [-21, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -28])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1590)) (countLit q [-21, -25]) (countLit q [-27, -28]) (count1590 q) 1 (meaning1588 q) (meaning1590 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1590 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1591 = true := by
  have hs : count1590 q = (countLit q [-21, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -28])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1591)) (countLit q [-21, -25]) (countLit q [-27, -28]) (count1590 q) 2 (meaning1589 q) (meaning1591 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1591 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1590 = true := by
  have hs : count1590 q = (countLit q [-21, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -28])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1590)) (countLit q [-21, -25]) (countLit q [-27, -28]) (count1590 q) 1 (meaning1586 q) (meaning1590 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1590 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1591 = true := by
  have hs : count1590 q = (countLit q [-21, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -28])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1591)) (countLit q [-21, -25]) (countLit q [-27, -28]) (count1590 q) 1 1 (meaning1586 q) (meaning1588 q) (meaning1591 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1588 = false ∨ valuation q 1591 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true := by
  have hs : count1590 q = (countLit q [-21, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -28])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1592)) (countLit q [-21, -25]) (countLit q [-27, -28]) (count1590 q) 1 2 (meaning1586 q) (meaning1589 q) (meaning1592 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1589 = false ∨ valuation q 1592 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1590 q = (countLit q [-21, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -28])
  have hm := merge_left (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-21, -25]) (countLit q [-27, -28]) (count1590 q) 2 (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1591 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1590 q = (countLit q [-21, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -28])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-21, -25]) (countLit q [-27, -28]) (count1590 q) 2 1 (meaning1587 q) (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1588 = false ∨ valuation q 1592 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1590 q = (countLit q [-21, -25]) + (countLit q [-27, -28]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -28])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-21, -25]) (countLit q [-27, -28]) (count1590 q) 2 2 (meaning1587 q) (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1589 = false ∨ valuation q 1593 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1594)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 1 (meaning1582 q) (meaning1594 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1594 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1595)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 1 1 (meaning1582 q) (meaning1590 q) (meaning1595 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1590 = false ∨ valuation q 1595 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1596)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 1 2 (meaning1582 q) (meaning1591 q) (meaning1596 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1591 = false ∨ valuation q 1596 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1597 = true := by
  have hs : count1594 q = (countLit q [-13, -16, -18, -19]) + (countLit q [-21, -25, -27, -28]) := List.countP_append (p := literal q) (l₁ := [-13, -16, -18, -19]) (l₂ := [-21, -25, -27, -28])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1597)) (countLit q [-13, -16, -18, -19]) (countLit q [-21, -25, -27, -28]) (count1594 q) 1 3 (meaning1582 q) (meaning1592 q) (meaning1597 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1592 = false ∨ valuation q 1597 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E050.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112050
