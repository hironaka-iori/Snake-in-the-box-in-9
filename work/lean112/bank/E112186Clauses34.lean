import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_left (literal (valuationOf q) (1648)) (literal (valuationOf q) (1660)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 2 (meaning1648 q) (meaning1660 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1660 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1661)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 2 1 (meaning1648 q) (meaning1655 q) (meaning1661 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1655 = false ∨ valuation q 1661 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1662)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 2 2 (meaning1648 q) (meaning1656 q) (meaning1662 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1656 = false ∨ valuation q 1662 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1663 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1663)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 2 3 (meaning1648 q) (meaning1657 q) (meaning1663 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1657 = false ∨ valuation q 1663 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1661 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_left (literal (valuationOf q) (1649)) (literal (valuationOf q) (1661)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 3 (meaning1649 q) (meaning1661 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1661 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1662 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1662)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 3 1 (meaning1649 q) (meaning1655 q) (meaning1662 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1655 = false ∨ valuation q 1662 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1663 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1663)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 3 2 (meaning1649 q) (meaning1656 q) (meaning1663 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1656 = false ∨ valuation q 1663 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1664 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1664)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 3 3 (meaning1649 q) (meaning1657 q) (meaning1664 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1657 = false ∨ valuation q 1664 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1650 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1663 = true := by
  have hs : count1659 q = (countLit q [-60, -62, -65, -66]) + (countLit q [-69, -70, -71, -75]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66]) (l₂ := [-69, -70, -71, -75])
  have hm := merge_two (literal (valuationOf q) (1650)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1663)) (countLit q [-60, -62, -65, -66]) (countLit q [-69, -70, -71, -75]) (count1659 q) 4 1 (meaning1650 q) (meaning1655 q) (meaning1663 q) hs
  change valuationOf q 1650 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1650 = false ∨ valuation q 1655 = false ∨ valuation q 1663 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1667 = true := by
  have hs : count1667 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1667)) (countLit q [-76]) (countLit q [-78]) (count1667 q) 1 (meaningNeg78 q) (meaning1667 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1667 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1667 = true := by
  have hs : count1667 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1667)) (countLit q [-76]) (countLit q [-78]) (count1667 q) 1 (meaningNeg76 q) (meaning1667 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1667 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1668 = true := by
  have hs : count1667 q = (countLit q [-76]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1668)) (countLit q [-76]) (countLit q [-78]) (count1667 q) 1 1 (meaningNeg76 q) (meaningNeg78 q) (meaning1668 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 78 = true ∨ valuation q 1668 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1669 = true := by
  have hs : count1669 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1669)) (countLit q [-81]) (countLit q [-83]) (count1669 q) 1 (meaningNeg83 q) (meaning1669 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1669 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1669 = true := by
  have hs : count1669 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1669)) (countLit q [-81]) (countLit q [-83]) (count1669 q) 1 (meaningNeg81 q) (meaning1669 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1669 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 83 = true ∨ valuationOf q 1670 = true := by
  have hs : count1669 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_two (literal (valuationOf q) (-81)) (literal (valuationOf q) (-83)) (literal (valuationOf q) (1670)) (countLit q [-81]) (countLit q [-83]) (count1669 q) 1 1 (meaningNeg81 q) (meaningNeg83 q) (meaning1670 q) hs
  change (! (valuationOf q 81)) = false ∨ (! (valuationOf q 83)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 83 = true ∨ valuation q 1670 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-76, -78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-81, -83])
  have hm := merge_right (literal (valuationOf q) (1669)) (literal (valuationOf q) (1671)) (countLit q [-76, -78]) (countLit q [-81, -83]) (count1671 q) 1 (meaning1669 q) (meaning1671 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1671 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1672 = true := by
  have hs : count1671 q = (countLit q [-76, -78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-81, -83])
  have hm := merge_right (literal (valuationOf q) (1670)) (literal (valuationOf q) (1672)) (countLit q [-76, -78]) (countLit q [-81, -83]) (count1671 q) 2 (meaning1670 q) (meaning1672 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1672 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-76, -78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-81, -83])
  have hm := merge_left (literal (valuationOf q) (1667)) (literal (valuationOf q) (1671)) (countLit q [-76, -78]) (countLit q [-81, -83]) (count1671 q) 1 (meaning1667 q) (meaning1671 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1671 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1672 = true := by
  have hs : count1671 q = (countLit q [-76, -78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-81, -83])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1672)) (countLit q [-76, -78]) (countLit q [-81, -83]) (count1671 q) 1 1 (meaning1667 q) (meaning1669 q) (meaning1672 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1669 = false ∨ valuation q 1672 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1673 = true := by
  have hs : count1671 q = (countLit q [-76, -78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-81, -83])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1673)) (countLit q [-76, -78]) (countLit q [-81, -83]) (count1671 q) 1 2 (meaning1667 q) (meaning1670 q) (meaning1673 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1670 = false ∨ valuation q 1673 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1672 = true := by
  have hs : count1671 q = (countLit q [-76, -78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-81, -83])
  have hm := merge_left (literal (valuationOf q) (1668)) (literal (valuationOf q) (1672)) (countLit q [-76, -78]) (countLit q [-81, -83]) (count1671 q) 2 (meaning1668 q) (meaning1672 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1672 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1673 = true := by
  have hs : count1671 q = (countLit q [-76, -78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-81, -83])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1673)) (countLit q [-76, -78]) (countLit q [-81, -83]) (count1671 q) 2 1 (meaning1668 q) (meaning1669 q) (meaning1673 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1669 = false ∨ valuation q 1673 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1674 = true := by
  have hs : count1671 q = (countLit q [-76, -78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-76, -78]) (l₂ := [-81, -83])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1674)) (countLit q [-76, -78]) (countLit q [-81, -83]) (count1671 q) 2 2 (meaning1668 q) (meaning1670 q) (meaning1674 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1670 = false ∨ valuation q 1674 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1675 = true := by
  have hs : count1675 q = (countLit q [-84]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1675)) (countLit q [-84]) (countLit q [-87]) (count1675 q) 1 (meaningNeg87 q) (meaning1675 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1675 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1675 = true := by
  have hs : count1675 q = (countLit q [-84]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1675)) (countLit q [-84]) (countLit q [-87]) (count1675 q) 1 (meaningNeg84 q) (meaning1675 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1675 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1676 = true := by
  have hs : count1675 q = (countLit q [-84]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1676)) (countLit q [-84]) (countLit q [-87]) (count1675 q) 1 1 (meaningNeg84 q) (meaningNeg87 q) (meaning1676 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 87 = true ∨ valuation q 1676 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1677 = true := by
  have hs : count1677 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1677)) (countLit q [-91]) (countLit q [-92]) (count1677 q) 1 (meaningNeg92 q) (meaning1677 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1677 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1677 = true := by
  have hs : count1677 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1677)) (countLit q [-91]) (countLit q [-92]) (count1677 q) 1 (meaningNeg91 q) (meaning1677 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1677 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1678 = true := by
  have hs : count1677 q = (countLit q [-91]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1678)) (countLit q [-91]) (countLit q [-92]) (count1677 q) 1 1 (meaningNeg91 q) (meaningNeg92 q) (meaning1678 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 92 = true ∨ valuation q 1678 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1679 = true := by
  have hs : count1679 q = (countLit q [-84, -87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -87]) (l₂ := [-91, -92])
  have hm := merge_right (literal (valuationOf q) (1677)) (literal (valuationOf q) (1679)) (countLit q [-84, -87]) (countLit q [-91, -92]) (count1679 q) 1 (meaning1677 q) (meaning1679 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1679 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-84, -87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -87]) (l₂ := [-91, -92])
  have hm := merge_right (literal (valuationOf q) (1678)) (literal (valuationOf q) (1680)) (countLit q [-84, -87]) (countLit q [-91, -92]) (count1679 q) 2 (meaning1678 q) (meaning1680 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1680 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1679 = true := by
  have hs : count1679 q = (countLit q [-84, -87]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-84, -87]) (l₂ := [-91, -92])
  have hm := merge_left (literal (valuationOf q) (1675)) (literal (valuationOf q) (1679)) (countLit q [-84, -87]) (countLit q [-91, -92]) (count1679 q) 1 (meaning1675 q) (meaning1679 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1679 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E186.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112186
