import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1660)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 1 6 (meaning1623 q) (meaning1651 q) (meaning1660 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1651 = false ∨ valuation q 1660 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1657)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 2 2 (meaning1624 q) (meaning1647 q) (meaning1657 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1647 = false ∨ valuation q 1657 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1658)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 2 3 (meaning1624 q) (meaning1648 q) (meaning1658 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1648 = false ∨ valuation q 1658 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1659)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 2 4 (meaning1624 q) (meaning1649 q) (meaning1659 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1649 = false ∨ valuation q 1659 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1660)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 2 5 (meaning1624 q) (meaning1650 q) (meaning1660 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1650 = false ∨ valuation q 1660 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1661)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 2 6 (meaning1624 q) (meaning1651 q) (meaning1661 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1651 = false ∨ valuation q 1661 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1657 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1657)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 3 1 (meaning1625 q) (meaning1646 q) (meaning1657 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1646 = false ∨ valuation q 1657 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1658)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 3 2 (meaning1625 q) (meaning1647 q) (meaning1658 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1647 = false ∨ valuation q 1658 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1659)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 3 3 (meaning1625 q) (meaning1648 q) (meaning1659 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1648 = false ∨ valuation q 1659 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1660)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 3 4 (meaning1625 q) (meaning1649 q) (meaning1660 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1649 = false ∨ valuation q 1660 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1661)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 3 5 (meaning1625 q) (meaning1650 q) (meaning1661 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1650 = false ∨ valuation q 1661 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1662)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 3 6 (meaning1625 q) (meaning1651 q) (meaning1662 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1651 = false ∨ valuation q 1662 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1658 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1658)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 4 1 (meaning1626 q) (meaning1646 q) (meaning1658 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1646 = false ∨ valuation q 1658 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1659)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 4 2 (meaning1626 q) (meaning1647 q) (meaning1659 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1647 = false ∨ valuation q 1659 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1660)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 4 3 (meaning1626 q) (meaning1648 q) (meaning1660 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1648 = false ∨ valuation q 1660 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1661)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 4 4 (meaning1626 q) (meaning1649 q) (meaning1661 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1649 = false ∨ valuation q 1661 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1662)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 4 5 (meaning1626 q) (meaning1650 q) (meaning1662 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1650 = false ∨ valuation q 1662 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1663 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1651)) (literal (valuationOf q) (1663)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 4 6 (meaning1626 q) (meaning1651 q) (meaning1663 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1651 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1651 = false ∨ valuation q 1663 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1659 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1659)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 5 1 (meaning1627 q) (meaning1646 q) (meaning1659 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1646 = false ∨ valuation q 1659 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1660 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1660)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 5 2 (meaning1627 q) (meaning1647 q) (meaning1660 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1647 = false ∨ valuation q 1660 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1661)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 5 3 (meaning1627 q) (meaning1648 q) (meaning1661 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1648 = false ∨ valuation q 1661 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1662)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 5 4 (meaning1627 q) (meaning1649 q) (meaning1662 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1649 = false ∨ valuation q 1662 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1650)) (literal (valuationOf q) (1663)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 5 5 (meaning1627 q) (meaning1650 q) (meaning1663 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1650 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1650 = false ∨ valuation q 1663 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1661 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1647)) (literal (valuationOf q) (1661)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 6 2 (meaning1628 q) (meaning1647 q) (meaning1661 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1647 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1647 = false ∨ valuation q 1661 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1662 = true := by
  have hs : count1654 q = (countLit q [-88, -89, -92, -95, -96, -99, -100]) + (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92, -95, -96, -99, -100]) (l₂ := [-104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1662)) (countLit q [-88, -89, -92, -95, -96, -99, -100]) (countLit q [-104, -107, -109, -110, -112, -113, -115, -117]) (count1654 q) 6 3 (meaning1628 q) (meaning1648 q) (meaning1662 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1648 = false ∨ valuation q 1662 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1676 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1676)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 2 6 (meaning1596 q) (meaning1659 q) (meaning1676 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1659 = false ∨ valuation q 1676 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1677)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 2 7 (meaning1596 q) (meaning1660 q) (meaning1677 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1660 = false ∨ valuation q 1677 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1678 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1678)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 2 8 (meaning1596 q) (meaning1661 q) (meaning1678 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1661 = false ∨ valuation q 1678 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1679 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1679)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 2 9 (meaning1596 q) (meaning1662 q) (meaning1679 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1662 = false ∨ valuation q 1679 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1680)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 2 10 (meaning1596 q) (meaning1663 q) (meaning1680 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1663 = false ∨ valuation q 1680 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1676 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1676)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 3 5 (meaning1597 q) (meaning1658 q) (meaning1676 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1658 = false ∨ valuation q 1676 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1677 = true := by
  have hs : count1669 q = (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) + (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (l₂ := [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1677)) (countLit q [-60, -61, -63, -64, -66, -68, -69, -72, -73, -77, -78, -79, -82, -84, -86]) (countLit q [-88, -89, -92, -95, -96, -99, -100, -104, -107, -109, -110, -112, -113, -115, -117]) (count1669 q) 3 6 (meaning1597 q) (meaning1659 q) (meaning1677 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1659 = false ∨ valuation q 1677 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E110.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112110
