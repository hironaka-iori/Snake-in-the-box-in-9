import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1645 = true := by
  have hs : count1645 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1645)) (countLit q [-65]) (countLit q [-66]) (count1645 q) 1 (meaningNeg65 q) (meaning1645 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1645 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1646 = true := by
  have hs : count1645 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1646)) (countLit q [-65]) (countLit q [-66]) (count1645 q) 1 1 (meaningNeg65 q) (meaningNeg66 q) (meaning1646 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 66 = true ∨ valuation q 1646 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-60, -62]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60, -62]) (l₂ := [-65, -66])
  have hm := merge_right (literal (valuationOf q) (1645)) (literal (valuationOf q) (1647)) (countLit q [-60, -62]) (countLit q [-65, -66]) (count1647 q) 1 (meaning1645 q) (meaning1647 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1647 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-60, -62]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60, -62]) (l₂ := [-65, -66])
  have hm := merge_right (literal (valuationOf q) (1646)) (literal (valuationOf q) (1648)) (countLit q [-60, -62]) (countLit q [-65, -66]) (count1647 q) 2 (meaning1646 q) (meaning1648 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1648 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1647 q = (countLit q [-60, -62]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60, -62]) (l₂ := [-65, -66])
  have hm := merge_left (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-60, -62]) (countLit q [-65, -66]) (count1647 q) 1 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-60, -62]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60, -62]) (l₂ := [-65, -66])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1648)) (countLit q [-60, -62]) (countLit q [-65, -66]) (count1647 q) 1 1 (meaning1643 q) (meaning1645 q) (meaning1648 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1645 = false ∨ valuation q 1648 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1649 = true := by
  have hs : count1647 q = (countLit q [-60, -62]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60, -62]) (l₂ := [-65, -66])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1649)) (countLit q [-60, -62]) (countLit q [-65, -66]) (count1647 q) 1 2 (meaning1643 q) (meaning1646 q) (meaning1649 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1646 = false ∨ valuation q 1649 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1647 q = (countLit q [-60, -62]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60, -62]) (l₂ := [-65, -66])
  have hm := merge_left (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-60, -62]) (countLit q [-65, -66]) (count1647 q) 2 (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1649 = true := by
  have hs : count1647 q = (countLit q [-60, -62]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60, -62]) (l₂ := [-65, -66])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1649)) (countLit q [-60, -62]) (countLit q [-65, -66]) (count1647 q) 2 1 (meaning1644 q) (meaning1645 q) (meaning1649 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1645 = false ∨ valuation q 1649 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1650 = true := by
  have hs : count1647 q = (countLit q [-60, -62]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60, -62]) (l₂ := [-65, -66])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1650)) (countLit q [-60, -62]) (countLit q [-65, -66]) (count1647 q) 2 2 (meaning1644 q) (meaning1646 q) (meaning1650 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1646 = false ∨ valuation q 1650 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1651 = true := by
  have hs : count1651 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1651)) (countLit q [-69]) (countLit q [-70]) (count1651 q) 1 (meaningNeg70 q) (meaning1651 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1651 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1651 = true := by
  have hs : count1651 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1651)) (countLit q [-69]) (countLit q [-70]) (count1651 q) 1 (meaningNeg69 q) (meaning1651 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1651 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 70 = true ∨ valuationOf q 1652 = true := by
  have hs : count1651 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (1652)) (countLit q [-69]) (countLit q [-70]) (count1651 q) 1 1 (meaningNeg69 q) (meaningNeg70 q) (meaning1652 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 1652 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-71]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (1653)) (countLit q [-71]) (countLit q [-75]) (count1653 q) 1 (meaningNeg75 q) (meaning1653 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1653 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1653 = true := by
  have hs : count1653 q = (countLit q [-71]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1653)) (countLit q [-71]) (countLit q [-75]) (count1653 q) 1 (meaningNeg71 q) (meaning1653 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1653 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 75 = true ∨ valuationOf q 1654 = true := by
  have hs : count1653 q = (countLit q [-71]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (1654)) (countLit q [-71]) (countLit q [-75]) (count1653 q) 1 1 (meaningNeg71 q) (meaningNeg75 q) (meaning1654 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 75 = true ∨ valuation q 1654 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-69, -70]) + (countLit q [-71, -75]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-71, -75])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1655)) (countLit q [-69, -70]) (countLit q [-71, -75]) (count1655 q) 1 (meaning1653 q) (meaning1655 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1655 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-69, -70]) + (countLit q [-71, -75]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-71, -75])
  have hm := merge_right (literal (valuationOf q) (1654)) (literal (valuationOf q) (1656)) (countLit q [-69, -70]) (countLit q [-71, -75]) (count1655 q) 2 (meaning1654 q) (meaning1656 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1656 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1655 = true := by
  have hs : count1655 q = (countLit q [-69, -70]) + (countLit q [-71, -75]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-71, -75])
  have hm := merge_left (literal (valuationOf q) (1651)) (literal (valuationOf q) (1655)) (countLit q [-69, -70]) (countLit q [-71, -75]) (count1655 q) 1 (meaning1651 q) (meaning1655 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1655 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-69, -70]) + (countLit q [-71, -75]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-71, -75])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1656)) (countLit q [-69, -70]) (countLit q [-71, -75]) (count1655 q) 1 1 (meaning1651 q) (meaning1653 q) (meaning1656 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1653 = false ∨ valuation q 1656 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1651 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-69, -70]) + (countLit q [-71, -75]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-71, -75])
  have hm := merge_two (literal (valuationOf q) (1651)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1657)) (countLit q [-69, -70]) (countLit q [-71, -75]) (count1655 q) 1 2 (meaning1651 q) (meaning1654 q) (meaning1657 q) hs
  change valuationOf q 1651 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1651 = false ∨ valuation q 1654 = false ∨ valuation q 1657 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1656 = true := by
  have hs : count1655 q = (countLit q [-69, -70]) + (countLit q [-71, -75]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-71, -75])
  have hm := merge_left (literal (valuationOf q) (1652)) (literal (valuationOf q) (1656)) (countLit q [-69, -70]) (countLit q [-71, -75]) (count1655 q) 2 (meaning1652 q) (meaning1656 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1656 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1655 q = (countLit q [-69, -70]) + (countLit q [-71, -75]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-71, -75])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-69, -70]) (countLit q [-71, -75]) (count1655 q) 2 1 (meaning1652 q) (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1653 = false ∨ valuation q 1657 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1655 q = (countLit q [-69, -70]) + (countLit q [-71, -75]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-71, -75])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-69, -70]) (countLit q [-71, -75]) (count1655 q) 2 2 (meaning1652 q) (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1654 = false ∨ valuation q 1658 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_right (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 1 (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1659 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_right (literal (valuationOf q) (1656)) (literal (valuationOf q) (1660)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 2 (meaning1656 q) (meaning1660 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1660 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_right (literal (valuationOf q) (1657)) (literal (valuationOf q) (1661)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 3 (meaning1657 q) (meaning1661 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1661 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_right (literal (valuationOf q) (1658)) (literal (valuationOf q) (1662)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 4 (meaning1658 q) (meaning1662 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1662 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_left (literal (valuationOf q) (1647)) (literal (valuationOf q) (1659)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 1 (meaning1647 q) (meaning1659 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1659 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1660)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 1 1 (meaning1647 q) (meaning1655 q) (meaning1660 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1655 = false ∨ valuation q 1660 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1661)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 1 2 (meaning1647 q) (meaning1656 q) (meaning1661 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1656 = false ∨ valuation q 1661 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1662)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 1 3 (meaning1647 q) (meaning1657 q) (meaning1662 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1657 = false ∨ valuation q 1662 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E186.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112186
