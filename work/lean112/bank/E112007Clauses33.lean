import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1580 = true := by
  have hs : count1578 q = (countLit q [-67, -68]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1580)) (countLit q [-67, -68]) (countLit q [-72, -74]) (count1578 q) 2 1 (meaning1575 q) (meaning1576 q) (meaning1580 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1576 = false ∨ valuation q 1580 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1581 = true := by
  have hs : count1578 q = (countLit q [-67, -68]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-67, -68]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1581)) (countLit q [-67, -68]) (countLit q [-72, -74]) (count1578 q) 2 2 (meaning1575 q) (meaning1577 q) (meaning1581 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1577 = false ∨ valuation q 1581 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1582)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 1 (meaning1578 q) (meaning1582 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1582 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_right (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 2 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_right (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 3 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_left (literal (valuationOf q) (1571)) (literal (valuationOf q) (1582)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 1 (meaning1571 q) (meaning1582 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1582 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1583)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 1 1 (meaning1571 q) (meaning1578 q) (meaning1583 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1578 = false ∨ valuation q 1583 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1584)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 1 2 (meaning1571 q) (meaning1579 q) (meaning1584 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1579 = false ∨ valuation q 1584 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1585)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 1 3 (meaning1571 q) (meaning1580 q) (meaning1585 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1580 = false ∨ valuation q 1585 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1586)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 1 4 (meaning1571 q) (meaning1581 q) (meaning1586 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1581 = false ∨ valuation q 1586 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_left (literal (valuationOf q) (1572)) (literal (valuationOf q) (1583)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 2 (meaning1572 q) (meaning1583 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1583 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1584)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 2 1 (meaning1572 q) (meaning1578 q) (meaning1584 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1578 = false ∨ valuation q 1584 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true := by
  have hs : count1582 q = (countLit q [-61, -64, -65]) + (countLit q [-67, -68, -72, -74]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65]) (l₂ := [-67, -68, -72, -74])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1585)) (countLit q [-61, -64, -65]) (countLit q [-67, -68, -72, -74]) (count1582 q) 2 2 (meaning1572 q) (meaning1579 q) (meaning1585 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1579 = false ∨ valuation q 1585 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-77]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1589)) (countLit q [-77]) (countLit q [-81]) (count1589 q) 1 (meaningNeg81 q) (meaning1589 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1589 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-77]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1589)) (countLit q [-77]) (countLit q [-81]) (count1589 q) 1 (meaningNeg77 q) (meaning1589 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1589 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-77]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1590)) (countLit q [-77]) (countLit q [-81]) (count1589 q) 1 1 (meaningNeg77 q) (meaningNeg81 q) (meaning1590 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 81 = true ∨ valuation q 1590 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-77, -81]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77, -81])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1591)) (countLit q [-76]) (countLit q [-77, -81]) (count1591 q) 1 (meaning1589 q) (meaning1591 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1591 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-77, -81]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77, -81])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1592)) (countLit q [-76]) (countLit q [-77, -81]) (count1591 q) 2 (meaning1590 q) (meaning1592 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1592 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-77, -81]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77, -81])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1591)) (countLit q [-76]) (countLit q [-77, -81]) (count1591 q) 1 (meaningNeg76 q) (meaning1591 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1591 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-77, -81]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77, -81])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1592)) (countLit q [-76]) (countLit q [-77, -81]) (count1591 q) 1 1 (meaningNeg76 q) (meaning1589 q) (meaning1592 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1589 = false ∨ valuation q 1592 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-76]) + (countLit q [-77, -81]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-77, -81])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1593)) (countLit q [-76]) (countLit q [-77, -81]) (count1591 q) 1 2 (meaningNeg76 q) (meaning1590 q) (meaning1593 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1590 = false ∨ valuation q 1593 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1594)) (countLit q [-83]) (countLit q [-85]) (count1594 q) 1 (meaningNeg85 q) (meaning1594 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1594 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1594 = true := by
  have hs : count1594 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1594)) (countLit q [-83]) (countLit q [-85]) (count1594 q) 1 (meaningNeg83 q) (meaning1594 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1594 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1595 = true := by
  have hs : count1594 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1595)) (countLit q [-83]) (countLit q [-85]) (count1594 q) 1 1 (meaningNeg83 q) (meaningNeg85 q) (meaning1595 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 85 = true ∨ valuation q 1595 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-86]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1596)) (countLit q [-86]) (countLit q [-90]) (count1596 q) 1 (meaningNeg90 q) (meaning1596 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1596 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-86]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1596)) (countLit q [-86]) (countLit q [-90]) (count1596 q) 1 (meaningNeg86 q) (meaning1596 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1596 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-86]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1597)) (countLit q [-86]) (countLit q [-90]) (count1596 q) 1 1 (meaningNeg86 q) (meaningNeg90 q) (meaning1597 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 90 = true ∨ valuation q 1597 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-83, -85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -85]) (l₂ := [-86, -90])
  have hm := merge_right (literal (valuationOf q) (1596)) (literal (valuationOf q) (1598)) (countLit q [-83, -85]) (countLit q [-86, -90]) (count1598 q) 1 (meaning1596 q) (meaning1598 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1598 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-83, -85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -85]) (l₂ := [-86, -90])
  have hm := merge_right (literal (valuationOf q) (1597)) (literal (valuationOf q) (1599)) (countLit q [-83, -85]) (countLit q [-86, -90]) (count1598 q) 2 (meaning1597 q) (meaning1599 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1599 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-83, -85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -85]) (l₂ := [-86, -90])
  have hm := merge_left (literal (valuationOf q) (1594)) (literal (valuationOf q) (1598)) (countLit q [-83, -85]) (countLit q [-86, -90]) (count1598 q) 1 (meaning1594 q) (meaning1598 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1598 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-83, -85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -85]) (l₂ := [-86, -90])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1599)) (countLit q [-83, -85]) (countLit q [-86, -90]) (count1598 q) 1 1 (meaning1594 q) (meaning1596 q) (meaning1599 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1596 = false ∨ valuation q 1599 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1600 = true := by
  have hs : count1598 q = (countLit q [-83, -85]) + (countLit q [-86, -90]) := List.countP_append (p := literal q) (l₁ := [-83, -85]) (l₂ := [-86, -90])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1597)) (literal (valuationOf q) (1600)) (countLit q [-83, -85]) (countLit q [-86, -90]) (count1598 q) 1 2 (meaning1594 q) (meaning1597 q) (meaning1600 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1597 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1597 = false ∨ valuation q 1600 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E007.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112007
