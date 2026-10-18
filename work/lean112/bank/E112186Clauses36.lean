import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1694)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 1 3 (meaning1659 q) (meaning1685 q) (meaning1694 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1685 = false ∨ valuation q 1694 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1695)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 1 4 (meaning1659 q) (meaning1686 q) (meaning1695 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1686 = false ∨ valuation q 1695 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1696)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 1 5 (meaning1659 q) (meaning1687 q) (meaning1696 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1687 = false ∨ valuation q 1696 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 1 6 (meaning1659 q) (meaning1688 q) (meaning1697 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1688 = false ∨ valuation q 1697 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1659)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 1 7 (meaning1659 q) (meaning1689 q) (meaning1698 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1689 = false ∨ valuation q 1698 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1693 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1693)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 2 1 (meaning1660 q) (meaning1683 q) (meaning1693 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1693 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1683 = false ∨ valuation q 1693 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1694)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 2 2 (meaning1660 q) (meaning1684 q) (meaning1694 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1684 = false ∨ valuation q 1694 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1695)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 2 3 (meaning1660 q) (meaning1685 q) (meaning1695 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1685 = false ∨ valuation q 1695 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1696)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 2 4 (meaning1660 q) (meaning1686 q) (meaning1696 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1686 = false ∨ valuation q 1696 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 2 5 (meaning1660 q) (meaning1687 q) (meaning1697 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1687 = false ∨ valuation q 1697 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 2 6 (meaning1660 q) (meaning1688 q) (meaning1698 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1688 = false ∨ valuation q 1698 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1660)) (literal (valuationOf q) (1689)) (literal (valuationOf q) (1699)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 2 7 (meaning1660 q) (meaning1689 q) (meaning1699 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1689 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1689 = false ∨ valuation q 1699 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1694)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 3 1 (meaning1661 q) (meaning1683 q) (meaning1694 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1683 = false ∨ valuation q 1694 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1695)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 3 2 (meaning1661 q) (meaning1684 q) (meaning1695 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1684 = false ∨ valuation q 1695 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1696)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 3 3 (meaning1661 q) (meaning1685 q) (meaning1696 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1685 = false ∨ valuation q 1696 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 3 4 (meaning1661 q) (meaning1686 q) (meaning1697 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1686 = false ∨ valuation q 1697 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 3 5 (meaning1661 q) (meaning1687 q) (meaning1698 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1687 = false ∨ valuation q 1698 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1661)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1699)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 3 6 (meaning1661 q) (meaning1688 q) (meaning1699 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1688 = false ∨ valuation q 1699 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1694 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_left (literal (valuationOf q) (1662)) (literal (valuationOf q) (1694)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 4 (meaning1662 q) (meaning1694 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1694 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1694 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1695 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1695)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 4 1 (meaning1662 q) (meaning1683 q) (meaning1695 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1695 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1683 = false ∨ valuation q 1695 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1696 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1696)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 4 2 (meaning1662 q) (meaning1684 q) (meaning1696 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1696 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1684 = false ∨ valuation q 1696 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 4 3 (meaning1662 q) (meaning1685 q) (meaning1697 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1685 = false ∨ valuation q 1697 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 4 4 (meaning1662 q) (meaning1686 q) (meaning1698 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1686 = false ∨ valuation q 1698 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1699 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1699)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 4 5 (meaning1662 q) (meaning1687 q) (meaning1699 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1687 = false ∨ valuation q 1699 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1662)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1700)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 4 6 (meaning1662 q) (meaning1688 q) (meaning1700 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1700 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1688 = false ∨ valuation q 1700 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1697 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1697)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 5 2 (meaning1663 q) (meaning1684 q) (meaning1697 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1697 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1684 = false ∨ valuation q 1697 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1698 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1698)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 5 3 (meaning1663 q) (meaning1685 q) (meaning1698 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1698 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1685 = false ∨ valuation q 1698 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1699 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1663)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1699)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 5 4 (meaning1663 q) (meaning1686 q) (meaning1699 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1686 = false ∨ valuation q 1699 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1699 = true := by
  have hs : count1691 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) + (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75]) (l₂ := [-76, -78, -81, -83, -84, -87, -91, -92])
  have hm := merge_two (literal (valuationOf q) (1664)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1699)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75]) (countLit q [-76, -78, -81, -83, -84, -87, -91, -92]) (count1691 q) 6 3 (meaning1664 q) (meaning1685 q) (meaning1699 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1699 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1685 = false ∨ valuation q 1699 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-94]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1707)) (countLit q [-94]) (countLit q [-97]) (count1707 q) 1 (meaningNeg97 q) (meaning1707 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1707 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1707 = true := by
  have hs : count1707 q = (countLit q [-94]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1707)) (countLit q [-94]) (countLit q [-97]) (count1707 q) 1 (meaningNeg94 q) (meaning1707 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1707 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1708 = true := by
  have hs : count1707 q = (countLit q [-94]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1708)) (countLit q [-94]) (countLit q [-97]) (count1707 q) 1 1 (meaningNeg94 q) (meaningNeg97 q) (meaning1708 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 97 = true ∨ valuation q 1708 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E186.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112186
