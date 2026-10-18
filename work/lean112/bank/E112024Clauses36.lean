import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-91, -93]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-94, -96])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1658)) (countLit q [-91, -93]) (countLit q [-94, -96]) (count1657 q) 1 1 (meaning1653 q) (meaning1655 q) (meaning1658 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1655 = false ∨ valuation q 1658 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1659 = true := by
  have hs : count1657 q = (countLit q [-91, -93]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-94, -96])
  have hm := merge_two (literal (valuationOf q) (1653)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1659)) (countLit q [-91, -93]) (countLit q [-94, -96]) (count1657 q) 1 2 (meaning1653 q) (meaning1656 q) (meaning1659 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1656 = false ∨ valuation q 1659 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-91, -93]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-94, -96])
  have hm := merge_left (literal (valuationOf q) (1654)) (literal (valuationOf q) (1658)) (countLit q [-91, -93]) (countLit q [-94, -96]) (count1657 q) 2 (meaning1654 q) (meaning1658 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1658 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1659 = true := by
  have hs : count1657 q = (countLit q [-91, -93]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-94, -96])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1659)) (countLit q [-91, -93]) (countLit q [-94, -96]) (count1657 q) 2 1 (meaning1654 q) (meaning1655 q) (meaning1659 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1655 = false ∨ valuation q 1659 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1660 = true := by
  have hs : count1657 q = (countLit q [-91, -93]) + (countLit q [-94, -96]) := List.countP_append (p := literal q) (l₁ := [-91, -93]) (l₂ := [-94, -96])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1660)) (countLit q [-91, -93]) (countLit q [-94, -96]) (count1657 q) 2 2 (meaning1654 q) (meaning1656 q) (meaning1660 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1656 = false ∨ valuation q 1660 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1661 = true := by
  have hs : count1661 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1661)) (countLit q [-98]) (countLit q [-99]) (count1661 q) 1 (meaningNeg99 q) (meaning1661 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1661 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1661 = true := by
  have hs : count1661 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1661)) (countLit q [-98]) (countLit q [-99]) (count1661 q) 1 (meaningNeg98 q) (meaning1661 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1661 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1662)) (countLit q [-98]) (countLit q [-99]) (count1661 q) 1 1 (meaningNeg98 q) (meaningNeg99 q) (meaning1662 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 1662 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1663)) (countLit q [-102]) (countLit q [-105]) (count1663 q) 1 (meaningNeg105 q) (meaning1663 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1663 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1663 = true := by
  have hs : count1663 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-102)) (literal (valuationOf q) (1663)) (countLit q [-102]) (countLit q [-105]) (count1663 q) 1 (meaningNeg102 q) (meaning1663 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1663 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1664 = true := by
  have hs : count1663 q = (countLit q [-102]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-102]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-102)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1664)) (countLit q [-102]) (countLit q [-105]) (count1663 q) 1 1 (meaningNeg102 q) (meaningNeg105 q) (meaning1664 q) hs
  change (! (valuationOf q 102)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 105 = true ∨ valuation q 1664 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_right (literal (valuationOf q) (1663)) (literal (valuationOf q) (1665)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1665 q) 1 (meaning1663 q) (meaning1665 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1665 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_right (literal (valuationOf q) (1664)) (literal (valuationOf q) (1666)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1665 q) 2 (meaning1664 q) (meaning1666 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1666 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_left (literal (valuationOf q) (1661)) (literal (valuationOf q) (1665)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1665 q) 1 (meaning1661 q) (meaning1665 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1665 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1666)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1665 q) 1 1 (meaning1661 q) (meaning1663 q) (meaning1666 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1663 = false ∨ valuation q 1666 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1667)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1665 q) 1 2 (meaning1661 q) (meaning1664 q) (meaning1667 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1664 = false ∨ valuation q 1667 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_left (literal (valuationOf q) (1662)) (literal (valuationOf q) (1666)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1665 q) 2 (meaning1662 q) (meaning1666 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1666 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1667)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1665 q) 2 1 (meaning1662 q) (meaning1663 q) (meaning1667 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1663 = false ∨ valuation q 1667 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1668 = true := by
  have hs : count1665 q = (countLit q [-98, -99]) + (countLit q [-102, -105]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-102, -105])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1668)) (countLit q [-98, -99]) (countLit q [-102, -105]) (count1665 q) 2 2 (meaning1662 q) (meaning1664 q) (meaning1668 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1664 = false ∨ valuation q 1668 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1665 = false ∨ valuationOf q 1669 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_right (literal (valuationOf q) (1665)) (literal (valuationOf q) (1669)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 1 (meaning1665 q) (meaning1669 q) hs
  change valuationOf q 1665 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1665 = false ∨ valuation q 1669 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1666 = false ∨ valuationOf q 1670 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_right (literal (valuationOf q) (1666)) (literal (valuationOf q) (1670)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 (meaning1666 q) (meaning1670 q) hs
  change valuationOf q 1666 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1666 = false ∨ valuation q 1670 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1671 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_right (literal (valuationOf q) (1667)) (literal (valuationOf q) (1671)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 3 (meaning1667 q) (meaning1671 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1671 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1669 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_left (literal (valuationOf q) (1657)) (literal (valuationOf q) (1669)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 1 (meaning1657 q) (meaning1669 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1669 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1670 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1670)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 1 1 (meaning1657 q) (meaning1665 q) (meaning1670 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1665 = false ∨ valuation q 1670 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1671 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1671)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 1 2 (meaning1657 q) (meaning1666 q) (meaning1671 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1666 = false ∨ valuation q 1671 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1672 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1672)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 1 3 (meaning1657 q) (meaning1667 q) (meaning1672 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1667 = false ∨ valuation q 1672 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1673 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1673)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 1 4 (meaning1657 q) (meaning1668 q) (meaning1673 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1668 = false ∨ valuation q 1673 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1670 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_left (literal (valuationOf q) (1658)) (literal (valuationOf q) (1670)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 (meaning1658 q) (meaning1670 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1670 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1671 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1671)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 1 (meaning1658 q) (meaning1665 q) (meaning1671 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1665 = false ∨ valuation q 1671 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1672 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1672)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 2 (meaning1658 q) (meaning1666 q) (meaning1672 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1666 = false ∨ valuation q 1672 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1673 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1673)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 3 (meaning1658 q) (meaning1667 q) (meaning1673 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1667 = false ∨ valuation q 1673 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1674 = true := by
  have hs : count1669 q = (countLit q [-91, -93, -94, -96]) + (countLit q [-98, -99, -102, -105]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96]) (l₂ := [-98, -99, -102, -105])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1674)) (countLit q [-91, -93, -94, -96]) (countLit q [-98, -99, -102, -105]) (count1669 q) 2 4 (meaning1658 q) (meaning1668 q) (meaning1674 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1668 = false ∨ valuation q 1674 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E024.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112024
