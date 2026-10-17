import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 106 = true ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-105]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-106])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-106)) (literal (valuationOf q) (1653)) (countLit q [-105]) (countLit q [-106]) (count1652 q) 1 1 (meaningNeg105 q) (meaningNeg106 q) (meaning1653 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 106)) = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 106 = true ∨ valuation q 1653 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 109 = true ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_right (literal (valuationOf q) (-109)) (literal (valuationOf q) (1654)) (countLit q [-107]) (countLit q [-109]) (count1654 q) 1 (meaningNeg109 q) (meaning1654 q) hs
  change (! (valuationOf q 109)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 109 = true ∨ valuation q 1654 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1654 = true := by
  have hs : count1654 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1654)) (countLit q [-107]) (countLit q [-109]) (count1654 q) 1 (meaningNeg107 q) (meaning1654 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1654 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 109 = true ∨ valuationOf q 1655 = true := by
  have hs : count1654 q = (countLit q [-107]) + (countLit q [-109]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-109])
  have hm := merge_two (literal (valuationOf q) (-107)) (literal (valuationOf q) (-109)) (literal (valuationOf q) (1655)) (countLit q [-107]) (countLit q [-109]) (count1654 q) 1 1 (meaningNeg107 q) (meaningNeg109 q) (meaning1655 q) hs
  change (! (valuationOf q 107)) = false ∨ (! (valuationOf q 109)) = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 109 = true ∨ valuation q 1655 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1656 = true := by
  have hs : count1656 q = (countLit q [-105, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1654)) (literal (valuationOf q) (1656)) (countLit q [-105, -106]) (countLit q [-107, -109]) (count1656 q) 1 (meaning1654 q) (meaning1656 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1656 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1657 = true := by
  have hs : count1656 q = (countLit q [-105, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -109])
  have hm := merge_right (literal (valuationOf q) (1655)) (literal (valuationOf q) (1657)) (countLit q [-105, -106]) (countLit q [-107, -109]) (count1656 q) 2 (meaning1655 q) (meaning1657 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1657 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1656 = true := by
  have hs : count1656 q = (countLit q [-105, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1652)) (literal (valuationOf q) (1656)) (countLit q [-105, -106]) (countLit q [-107, -109]) (count1656 q) 1 (meaning1652 q) (meaning1656 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1656 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1656 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1657 = true := by
  have hs : count1656 q = (countLit q [-105, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1657)) (countLit q [-105, -106]) (countLit q [-107, -109]) (count1656 q) 1 1 (meaning1652 q) (meaning1654 q) (meaning1657 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1654 = false ∨ valuation q 1657 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1658 = true := by
  have hs : count1656 q = (countLit q [-105, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1652)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1658)) (countLit q [-105, -106]) (countLit q [-107, -109]) (count1656 q) 1 2 (meaning1652 q) (meaning1655 q) (meaning1658 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1655 = false ∨ valuation q 1658 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1657 = true := by
  have hs : count1656 q = (countLit q [-105, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1653)) (literal (valuationOf q) (1657)) (countLit q [-105, -106]) (countLit q [-107, -109]) (count1656 q) 2 (meaning1653 q) (meaning1657 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1657 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1656 q = (countLit q [-105, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-105, -106]) (countLit q [-107, -109]) (count1656 q) 2 1 (meaning1653 q) (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1654 = false ∨ valuation q 1658 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1656 q = (countLit q [-105, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-105, -106]) (l₂ := [-107, -109])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-105, -106]) (countLit q [-107, -109]) (count1656 q) 2 2 (meaning1653 q) (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1655 = false ∨ valuation q 1659 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 1660 = true := by
  have hs : count1660 q = (countLit q [-112]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-115])
  have hm := merge_right (literal (valuationOf q) (-115)) (literal (valuationOf q) (1660)) (countLit q [-112]) (countLit q [-115]) (count1660 q) 1 (meaningNeg115 q) (meaning1660 q) hs
  change (! (valuationOf q 115)) = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 1660 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1660 = true := by
  have hs : count1660 q = (countLit q [-112]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-115])
  have hm := merge_left (literal (valuationOf q) (-112)) (literal (valuationOf q) (1660)) (countLit q [-112]) (countLit q [-115]) (count1660 q) 1 (meaningNeg112 q) (meaning1660 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1660 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 115 = true ∨ valuationOf q 1661 = true := by
  have hs : count1660 q = (countLit q [-112]) + (countLit q [-115]) := List.countP_append (p := literal q) (l₁ := [-112]) (l₂ := [-115])
  have hm := merge_two (literal (valuationOf q) (-112)) (literal (valuationOf q) (-115)) (literal (valuationOf q) (1661)) (countLit q [-112]) (countLit q [-115]) (count1660 q) 1 1 (meaningNeg112 q) (meaningNeg115 q) (meaning1661 q) hs
  change (! (valuationOf q 112)) = false ∨ (! (valuationOf q 115)) = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 115 = true ∨ valuation q 1661 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 118 = true ∨ valuationOf q 1662 = true := by
  have hs : count1662 q = (countLit q [-116]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-118])
  have hm := merge_right (literal (valuationOf q) (-118)) (literal (valuationOf q) (1662)) (countLit q [-116]) (countLit q [-118]) (count1662 q) 1 (meaningNeg118 q) (meaning1662 q) hs
  change (! (valuationOf q 118)) = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 118 = true ∨ valuation q 1662 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1662 = true := by
  have hs : count1662 q = (countLit q [-116]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-118])
  have hm := merge_left (literal (valuationOf q) (-116)) (literal (valuationOf q) (1662)) (countLit q [-116]) (countLit q [-118]) (count1662 q) 1 (meaningNeg116 q) (meaning1662 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1662 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 118 = true ∨ valuationOf q 1663 = true := by
  have hs : count1662 q = (countLit q [-116]) + (countLit q [-118]) := List.countP_append (p := literal q) (l₁ := [-116]) (l₂ := [-118])
  have hm := merge_two (literal (valuationOf q) (-116)) (literal (valuationOf q) (-118)) (literal (valuationOf q) (1663)) (countLit q [-116]) (countLit q [-118]) (count1662 q) 1 1 (meaningNeg116 q) (meaningNeg118 q) (meaning1663 q) hs
  change (! (valuationOf q 116)) = false ∨ (! (valuationOf q 118)) = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 118 = true ∨ valuation q 1663 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1664 = true := by
  have hs : count1664 q = (countLit q [-112, -115]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -115]) (l₂ := [-116, -118])
  have hm := merge_right (literal (valuationOf q) (1662)) (literal (valuationOf q) (1664)) (countLit q [-112, -115]) (countLit q [-116, -118]) (count1664 q) 1 (meaning1662 q) (meaning1664 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1664 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-112, -115]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -115]) (l₂ := [-116, -118])
  have hm := merge_right (literal (valuationOf q) (1663)) (literal (valuationOf q) (1665)) (countLit q [-112, -115]) (countLit q [-116, -118]) (count1664 q) 2 (meaning1663 q) (meaning1665 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1665 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1664 = true := by
  have hs : count1664 q = (countLit q [-112, -115]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -115]) (l₂ := [-116, -118])
  have hm := merge_left (literal (valuationOf q) (1660)) (literal (valuationOf q) (1664)) (countLit q [-112, -115]) (countLit q [-116, -118]) (count1664 q) 1 (meaning1660 q) (meaning1664 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1664 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-112, -115]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -115]) (l₂ := [-116, -118])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1665)) (countLit q [-112, -115]) (countLit q [-116, -118]) (count1664 q) 1 1 (meaning1660 q) (meaning1662 q) (meaning1665 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1662 = false ∨ valuation q 1665 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1666 = true := by
  have hs : count1664 q = (countLit q [-112, -115]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -115]) (l₂ := [-116, -118])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1666)) (countLit q [-112, -115]) (countLit q [-116, -118]) (count1664 q) 1 2 (meaning1660 q) (meaning1663 q) (meaning1666 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1663 = false ∨ valuation q 1666 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1665 = true := by
  have hs : count1664 q = (countLit q [-112, -115]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -115]) (l₂ := [-116, -118])
  have hm := merge_left (literal (valuationOf q) (1661)) (literal (valuationOf q) (1665)) (countLit q [-112, -115]) (countLit q [-116, -118]) (count1664 q) 2 (meaning1661 q) (meaning1665 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1665 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1666 = true := by
  have hs : count1664 q = (countLit q [-112, -115]) + (countLit q [-116, -118]) := List.countP_append (p := literal q) (l₁ := [-112, -115]) (l₂ := [-116, -118])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1666)) (countLit q [-112, -115]) (countLit q [-116, -118]) (count1664 q) 2 1 (meaning1661 q) (meaning1662 q) (meaning1666 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1662 = false ∨ valuation q 1666 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1668 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_right (literal (valuationOf q) (1664)) (literal (valuationOf q) (1668)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 1 (meaning1664 q) (meaning1668 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1668 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1669 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_right (literal (valuationOf q) (1665)) (literal (valuationOf q) (1669)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 2 (meaning1665 q) (meaning1669 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1669 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1670 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_right (literal (valuationOf q) (1666)) (literal (valuationOf q) (1670)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 3 (meaning1666 q) (meaning1670 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1670 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1668 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_left (literal (valuationOf q) (1656)) (literal (valuationOf q) (1668)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 1 (meaning1656 q) (meaning1668 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1668 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1669 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1669)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 1 1 (meaning1656 q) (meaning1664 q) (meaning1669 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1664 = false ∨ valuation q 1669 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1670 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1670)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 1 2 (meaning1656 q) (meaning1665 q) (meaning1670 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1665 = false ∨ valuation q 1670 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1671 = true := by
  have hs : count1668 q = (countLit q [-105, -106, -107, -109]) + (countLit q [-112, -115, -116, -118]) := List.countP_append (p := literal q) (l₁ := [-105, -106, -107, -109]) (l₂ := [-112, -115, -116, -118])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1671)) (countLit q [-105, -106, -107, -109]) (countLit q [-112, -115, -116, -118]) (count1668 q) 1 3 (meaning1656 q) (meaning1666 q) (meaning1671 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1666 = false ∨ valuation q 1671 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E078.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112078
