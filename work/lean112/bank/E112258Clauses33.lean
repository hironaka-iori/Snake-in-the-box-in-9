import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1570)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 1 2 (meaning1557 q) (meaning1565 q) (meaning1570 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1565 = false ∨ valuation q 1570 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1571 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1571)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 1 3 (meaning1557 q) (meaning1566 q) (meaning1571 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1566 = false ∨ valuation q 1571 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_left (literal (valuationOf q) (1558)) (literal (valuationOf q) (1569)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 2 (meaning1558 q) (meaning1569 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1569 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1570)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 2 1 (meaning1558 q) (meaning1564 q) (meaning1570 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1564 = false ∨ valuation q 1570 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1571)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 2 2 (meaning1558 q) (meaning1565 q) (meaning1571 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1565 = false ∨ valuation q 1571 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_left (literal (valuationOf q) (1559)) (literal (valuationOf q) (1570)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 3 (meaning1559 q) (meaning1570 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1570 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1571 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1571)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 3 1 (meaning1559 q) (meaning1564 q) (meaning1571 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1564 = false ∨ valuation q 1571 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1572 = true := by
  have hs : count1568 q = (countLit q [-33, -35, -37]) + (countLit q [-39, -41, -43, -44]) := List.countP_append (p := literal q) (l₁ := [-33, -35, -37]) (l₂ := [-39, -41, -43, -44])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1572)) (countLit q [-33, -35, -37]) (countLit q [-39, -41, -43, -44]) (count1568 q) 3 2 (meaning1559 q) (meaning1565 q) (meaning1572 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1565 = false ∨ valuation q 1572 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-47]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (1575)) (countLit q [-47]) (countLit q [-50]) (count1575 q) 1 (meaningNeg50 q) (meaning1575 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 1575 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1577)) (countLit q [-51]) (countLit q [-52]) (count1577 q) 1 (meaningNeg52 q) (meaning1577 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1577 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1577)) (countLit q [-51]) (countLit q [-52]) (count1577 q) 1 (meaningNeg51 q) (meaning1577 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1577 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1578 = true := by
  have hs : count1577 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1578)) (countLit q [-51]) (countLit q [-52]) (count1577 q) 1 1 (meaningNeg51 q) (meaningNeg52 q) (meaning1578 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 1578 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-47, -50]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1577)) (literal (valuationOf q) (1579)) (countLit q [-47, -50]) (countLit q [-51, -52]) (count1579 q) 1 (meaning1577 q) (meaning1579 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1579 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-47, -50]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (countLit q [-47, -50]) (countLit q [-51, -52]) (count1579 q) 2 (meaning1578 q) (meaning1580 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-47, -50]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-51, -52])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1579)) (countLit q [-47, -50]) (countLit q [-51, -52]) (count1579 q) 1 (meaning1575 q) (meaning1579 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1579 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-47, -50]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47, -50]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1580)) (countLit q [-47, -50]) (countLit q [-51, -52]) (count1579 q) 1 1 (meaning1575 q) (meaning1577 q) (meaning1580 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1577 = false ∨ valuation q 1580 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1583)) (countLit q [-55]) (countLit q [-58]) (count1583 q) 1 (meaningNeg58 q) (meaning1583 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1583 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1583)) (countLit q [-55]) (countLit q [-58]) (count1583 q) 1 (meaningNeg55 q) (meaning1583 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1583 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 58 = true ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (1584)) (countLit q [-55]) (countLit q [-58]) (count1583 q) 1 1 (meaningNeg55 q) (meaningNeg58 q) (meaning1584 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 58 = true ∨ valuation q 1584 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_right (literal (valuationOf q) (-63)) (literal (valuationOf q) (1585)) (countLit q [-61]) (countLit q [-63]) (count1585 q) 1 (meaningNeg63 q) (meaning1585 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1585 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1585)) (countLit q [-61]) (countLit q [-63]) (count1585 q) 1 (meaningNeg61 q) (meaning1585 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1585 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 63 = true ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-61]) + (countLit q [-63]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (-63)) (literal (valuationOf q) (1586)) (countLit q [-61]) (countLit q [-63]) (count1585 q) 1 1 (meaningNeg61 q) (meaningNeg63 q) (meaning1586 q) hs
  change (! (valuationOf q 61)) = false ∨ (! (valuationOf q 63)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 63 = true ∨ valuation q 1586 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1585)) (literal (valuationOf q) (1587)) (countLit q [-55, -58]) (countLit q [-61, -63]) (count1587 q) 1 (meaning1585 q) (meaning1587 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1587 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-61, -63])
  have hm := merge_right (literal (valuationOf q) (1586)) (literal (valuationOf q) (1588)) (countLit q [-55, -58]) (countLit q [-61, -63]) (count1587 q) 2 (meaning1586 q) (meaning1588 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1588 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-61, -63])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-55, -58]) (countLit q [-61, -63]) (count1587 q) 1 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1588)) (countLit q [-55, -58]) (countLit q [-61, -63]) (count1587 q) 1 1 (meaning1583 q) (meaning1585 q) (meaning1588 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = false ∨ valuation q 1588 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-61, -63])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1588)) (countLit q [-55, -58]) (countLit q [-61, -63]) (count1587 q) 2 (meaning1584 q) (meaning1588 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1588 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-61, -63]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-61, -63])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-55, -58]) (countLit q [-61, -63]) (count1587 q) 2 1 (meaning1584 q) (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1585 = false ∨ valuation q 1589 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-47, -50, -51, -52]) + (countLit q [-55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -51, -52]) (l₂ := [-55, -58, -61, -63])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-47, -50, -51, -52]) (countLit q [-55, -58, -61, -63]) (count1591 q) 1 (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1591 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-47, -50, -51, -52]) + (countLit q [-55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -51, -52]) (l₂ := [-55, -58, -61, -63])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-47, -50, -51, -52]) (countLit q [-55, -58, -61, -63]) (count1591 q) 2 (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1592 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-47, -50, -51, -52]) + (countLit q [-55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -51, -52]) (l₂ := [-55, -58, -61, -63])
  have hm := merge_left (literal (valuationOf q) (1579)) (literal (valuationOf q) (1591)) (countLit q [-47, -50, -51, -52]) (countLit q [-55, -58, -61, -63]) (count1591 q) 1 (meaning1579 q) (meaning1591 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1591 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-47, -50, -51, -52]) + (countLit q [-55, -58, -61, -63]) := List.countP_append (p := literal q) (l₁ := [-47, -50, -51, -52]) (l₂ := [-55, -58, -61, -63])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1592)) (countLit q [-47, -50, -51, -52]) (countLit q [-55, -58, -61, -63]) (count1591 q) 1 1 (meaning1579 q) (meaning1587 q) (meaning1592 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1587 = false ∨ valuation q 1592 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E258.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112258
