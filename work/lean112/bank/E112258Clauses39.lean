import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1645)) (literal (valuationOf q) (1672)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 1 (meaning1645 q) (meaning1672 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1672 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1673 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1673)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 1 1 (meaning1645 q) (meaning1665 q) (meaning1673 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1665 = false ∨ valuation q 1673 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1674 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1674)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 1 2 (meaning1645 q) (meaning1666 q) (meaning1674 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1666 = false ∨ valuation q 1674 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1675 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1675)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 1 3 (meaning1645 q) (meaning1667 q) (meaning1675 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1667 = false ∨ valuation q 1675 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1676 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1676)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 1 4 (meaning1645 q) (meaning1668 q) (meaning1676 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1668 = false ∨ valuation q 1676 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1677 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1677)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 1 5 (meaning1645 q) (meaning1669 q) (meaning1677 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1669 = false ∨ valuation q 1677 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1678 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1678)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 1 6 (meaning1645 q) (meaning1670 q) (meaning1678 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1670 = false ∨ valuation q 1678 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1673 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1646)) (literal (valuationOf q) (1673)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 2 (meaning1646 q) (meaning1673 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1673 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1674 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1674)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 2 1 (meaning1646 q) (meaning1665 q) (meaning1674 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1665 = false ∨ valuation q 1674 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1675 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1675)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 2 2 (meaning1646 q) (meaning1666 q) (meaning1675 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1666 = false ∨ valuation q 1675 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1676 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1676)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 2 3 (meaning1646 q) (meaning1667 q) (meaning1676 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1667 = false ∨ valuation q 1676 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1677 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1677)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 2 4 (meaning1646 q) (meaning1668 q) (meaning1677 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1668 = false ∨ valuation q 1677 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1678 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1678)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 2 5 (meaning1646 q) (meaning1669 q) (meaning1678 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1669 = false ∨ valuation q 1678 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1679 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1646)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1679)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 2 6 (meaning1646 q) (meaning1670 q) (meaning1679 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1670 = false ∨ valuation q 1679 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1674 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1647)) (literal (valuationOf q) (1674)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 3 (meaning1647 q) (meaning1674 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1674 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1675 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1675)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 3 1 (meaning1647 q) (meaning1665 q) (meaning1675 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1665 = false ∨ valuation q 1675 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1676 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1676)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 3 2 (meaning1647 q) (meaning1666 q) (meaning1676 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1666 = false ∨ valuation q 1676 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1677 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1677)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 3 3 (meaning1647 q) (meaning1667 q) (meaning1677 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1667 = false ∨ valuation q 1677 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1678 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1678)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 3 4 (meaning1647 q) (meaning1668 q) (meaning1678 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1668 = false ∨ valuation q 1678 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1679 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1679)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 3 5 (meaning1647 q) (meaning1669 q) (meaning1679 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1669 = false ∨ valuation q 1679 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1680 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1647)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1680)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 3 6 (meaning1647 q) (meaning1670 q) (meaning1680 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1670 = false ∨ valuation q 1680 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1675 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1648)) (literal (valuationOf q) (1675)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 4 (meaning1648 q) (meaning1675 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1675 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1676 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1676)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 4 1 (meaning1648 q) (meaning1665 q) (meaning1676 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1665 = false ∨ valuation q 1676 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1677 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1677)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 4 2 (meaning1648 q) (meaning1666 q) (meaning1677 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1666 = false ∨ valuation q 1677 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1678 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1678)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 4 3 (meaning1648 q) (meaning1667 q) (meaning1678 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1667 = false ∨ valuation q 1678 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1679 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1679)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 4 4 (meaning1648 q) (meaning1668 q) (meaning1679 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1668 = false ∨ valuation q 1679 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1680 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1648)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1680)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 4 5 (meaning1648 q) (meaning1669 q) (meaning1680 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1669 = false ∨ valuation q 1680 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1676 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1649)) (literal (valuationOf q) (1676)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 5 (meaning1649 q) (meaning1676 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1676 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1677 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1677)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 5 1 (meaning1649 q) (meaning1665 q) (meaning1677 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1665 = false ∨ valuation q 1677 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1678 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1678)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 5 2 (meaning1649 q) (meaning1666 q) (meaning1678 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1666 = false ∨ valuation q 1678 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1679 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1679)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 5 3 (meaning1649 q) (meaning1667 q) (meaning1679 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1667 = false ∨ valuation q 1679 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1680 = true := by
  have hs : count1672 q = (countLit q [-65, -66, -67, -69, -73, -77, -78]) + (countLit q [-79, -81, -82, -84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -73, -77, -78]) (l₂ := [-79, -81, -82, -84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1649)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1680)) (countLit q [-65, -66, -67, -69, -73, -77, -78]) (countLit q [-79, -81, -82, -84, -85, -86, -88]) (count1672 q) 5 4 (meaning1649 q) (meaning1668 q) (meaning1680 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1668 = false ∨ valuation q 1680 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E258.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112258
