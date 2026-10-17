import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 4 (meaning1672 q) (meaning1696 q) (meaning1708 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1696 = false ∨ valuation q 1708 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1709 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1697)) (literal (valuationOf q) (1709)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 4 5 (meaning1672 q) (meaning1697 q) (meaning1709 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1697 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1697 = false ∨ valuation q 1709 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1706 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1706)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 1 (meaning1673 q) (meaning1693 q) (meaning1706 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1706 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1693 = false ∨ valuation q 1706 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 2 (meaning1673 q) (meaning1694 q) (meaning1707 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1694 = false ∨ valuation q 1707 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 3 (meaning1673 q) (meaning1695 q) (meaning1708 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1695 = false ∨ valuation q 1708 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1709 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1696)) (literal (valuationOf q) (1709)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 5 4 (meaning1673 q) (meaning1696 q) (meaning1709 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1696 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1696 = false ∨ valuation q 1709 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1707 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1707)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 6 1 (meaning1674 q) (meaning1693 q) (meaning1707 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1707 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1693 = false ∨ valuation q 1707 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 6 2 (meaning1674 q) (meaning1694 q) (meaning1708 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1694 = false ∨ valuation q 1708 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1709 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1695)) (literal (valuationOf q) (1709)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 6 3 (meaning1674 q) (meaning1695 q) (meaning1709 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1695 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1695 = false ∨ valuation q 1709 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1708 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1693)) (literal (valuationOf q) (1708)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 7 1 (meaning1675 q) (meaning1693 q) (meaning1708 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1693 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1693 = false ∨ valuation q 1708 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1709 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1709)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 7 2 (meaning1675 q) (meaning1694 q) (meaning1709 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1709 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1694 = false ∨ valuation q 1709 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1710 = true := by
  have hs : count1701 q = (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) + (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-91, -93, -94, -96, -98, -99, -102, -105]) (l₂ := [-107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1694)) (literal (valuationOf q) (1710)) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105]) (countLit q [-107, -108, -110, -111, -115, -117, -118, -119]) (count1701 q) 8 2 (meaning1676 q) (meaning1694 q) (meaning1710 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1694 = false ∨ valuationOf q 1710 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1694 = false ∨ valuation q 1710 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1725)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 1 8 (meaning1637 q) (meaning1708 q) (meaning1725 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1708 = false ∨ valuation q 1725 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1723 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1723)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 5 (meaning1638 q) (meaning1705 q) (meaning1723 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1705 = false ∨ valuation q 1723 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1724 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1724)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 6 (meaning1638 q) (meaning1706 q) (meaning1724 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1706 = false ∨ valuation q 1724 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1725)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 7 (meaning1638 q) (meaning1707 q) (meaning1725 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1707 = false ∨ valuation q 1725 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1726)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 8 (meaning1638 q) (meaning1708 q) (meaning1726 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1708 = false ∨ valuation q 1726 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1727)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 2 9 (meaning1638 q) (meaning1709 q) (meaning1727 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1709 = false ∨ valuation q 1727 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1723 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1723)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 4 (meaning1639 q) (meaning1704 q) (meaning1723 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1723 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1704 = false ∨ valuation q 1723 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1724 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1724)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 5 (meaning1639 q) (meaning1705 q) (meaning1724 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1705 = false ∨ valuation q 1724 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1725)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 6 (meaning1639 q) (meaning1706 q) (meaning1725 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1706 = false ∨ valuation q 1725 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1726)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 7 (meaning1639 q) (meaning1707 q) (meaning1726 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1707 = false ∨ valuation q 1726 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1727)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 8 (meaning1639 q) (meaning1708 q) (meaning1727 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1708 = false ∨ valuation q 1727 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1728)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 9 (meaning1639 q) (meaning1709 q) (meaning1728 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1709 = false ∨ valuation q 1728 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1724 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1724)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 4 (meaning1640 q) (meaning1704 q) (meaning1724 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1704 = false ∨ valuation q 1724 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1725)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 5 (meaning1640 q) (meaning1705 q) (meaning1725 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1705 = false ∨ valuation q 1725 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1726)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 6 (meaning1640 q) (meaning1706 q) (meaning1726 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1706 = false ∨ valuation q 1726 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1727)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 7 (meaning1640 q) (meaning1707 q) (meaning1727 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1707 = false ∨ valuation q 1727 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1728)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 8 (meaning1640 q) (meaning1708 q) (meaning1728 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1708 = false ∨ valuation q 1728 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1729)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 9 (meaning1640 q) (meaning1709 q) (meaning1729 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1709 = false ∨ valuation q 1729 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1730)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 10 (meaning1640 q) (meaning1710 q) (meaning1730 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1710 = false ∨ valuation q 1730 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1724 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1724)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 3 (meaning1641 q) (meaning1703 q) (meaning1724 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1703 = false ∨ valuation q 1724 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E024.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112024
