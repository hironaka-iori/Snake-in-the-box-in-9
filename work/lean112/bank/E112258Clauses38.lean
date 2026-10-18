import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1657)) (countLit q [-84]) (countLit q [-85]) (count1657 q) 1 (meaningNeg85 q) (meaning1657 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1657 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1657 = true := by
  have hs : count1657 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1657)) (countLit q [-84]) (countLit q [-85]) (count1657 q) 1 (meaningNeg84 q) (meaning1657 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1657 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1657 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1658 = true := by
  have hs : count1657 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1658)) (countLit q [-84]) (countLit q [-85]) (count1657 q) 1 1 (meaningNeg84 q) (meaningNeg85 q) (meaning1658 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1658 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 85 = true ∨ valuation q 1658 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_right (literal (valuationOf q) (-88)) (literal (valuationOf q) (1659)) (countLit q [-86]) (countLit q [-88]) (count1659 q) 1 (meaningNeg88 q) (meaning1659 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1659 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1659 = true := by
  have hs : count1659 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1659)) (countLit q [-86]) (countLit q [-88]) (count1659 q) 1 (meaningNeg86 q) (meaning1659 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1659 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1659 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 88 = true ∨ valuationOf q 1660 = true := by
  have hs : count1659 q = (countLit q [-86]) + (countLit q [-88]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-88])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-88)) (literal (valuationOf q) (1660)) (countLit q [-86]) (countLit q [-88]) (count1659 q) 1 1 (meaningNeg86 q) (meaningNeg88 q) (meaning1660 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 88)) = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 88 = true ∨ valuation q 1660 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1659 = false ∨ valuationOf q 1661 = true := by
  have hs : count1661 q = (countLit q [-84, -85]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-86, -88])
  have hm := merge_right (literal (valuationOf q) (1659)) (literal (valuationOf q) (1661)) (countLit q [-84, -85]) (countLit q [-86, -88]) (count1661 q) 1 (meaning1659 q) (meaning1661 q) hs
  change valuationOf q 1659 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1659 = false ∨ valuation q 1661 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1660 = false ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-84, -85]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-86, -88])
  have hm := merge_right (literal (valuationOf q) (1660)) (literal (valuationOf q) (1662)) (countLit q [-84, -85]) (countLit q [-86, -88]) (count1661 q) 2 (meaning1660 q) (meaning1662 q) hs
  change valuationOf q 1660 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1660 = false ∨ valuation q 1662 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1661 = true := by
  have hs : count1661 q = (countLit q [-84, -85]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-86, -88])
  have hm := merge_left (literal (valuationOf q) (1657)) (literal (valuationOf q) (1661)) (countLit q [-84, -85]) (countLit q [-86, -88]) (count1661 q) 1 (meaning1657 q) (meaning1661 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1661 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-84, -85]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1662)) (countLit q [-84, -85]) (countLit q [-86, -88]) (count1661 q) 1 1 (meaning1657 q) (meaning1659 q) (meaning1662 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1659 = false ∨ valuation q 1662 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1657 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1663 = true := by
  have hs : count1661 q = (countLit q [-84, -85]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (1657)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1663)) (countLit q [-84, -85]) (countLit q [-86, -88]) (count1661 q) 1 2 (meaning1657 q) (meaning1660 q) (meaning1663 q) hs
  change valuationOf q 1657 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1657 = false ∨ valuation q 1660 = false ∨ valuation q 1663 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1662 = true := by
  have hs : count1661 q = (countLit q [-84, -85]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-86, -88])
  have hm := merge_left (literal (valuationOf q) (1658)) (literal (valuationOf q) (1662)) (countLit q [-84, -85]) (countLit q [-86, -88]) (count1661 q) 2 (meaning1658 q) (meaning1662 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1662 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1663 = true := by
  have hs : count1661 q = (countLit q [-84, -85]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1663)) (countLit q [-84, -85]) (countLit q [-86, -88]) (count1661 q) 2 1 (meaning1658 q) (meaning1659 q) (meaning1663 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1659 = false ∨ valuation q 1663 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1658 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1664 = true := by
  have hs : count1661 q = (countLit q [-84, -85]) + (countLit q [-86, -88]) := List.countP_append (p := literal q) (l₁ := [-84, -85]) (l₂ := [-86, -88])
  have hm := merge_two (literal (valuationOf q) (1658)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1664)) (countLit q [-84, -85]) (countLit q [-86, -88]) (count1661 q) 2 2 (meaning1658 q) (meaning1660 q) (meaning1664 q) hs
  change valuationOf q 1658 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1658 = false ∨ valuation q 1660 = false ∨ valuation q 1664 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1661 = false ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_right (literal (valuationOf q) (1661)) (literal (valuationOf q) (1665)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 1 (meaning1661 q) (meaning1665 q) hs
  change valuationOf q 1661 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1661 = false ∨ valuation q 1665 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1662 = false ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_right (literal (valuationOf q) (1662)) (literal (valuationOf q) (1666)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 2 (meaning1662 q) (meaning1666 q) hs
  change valuationOf q 1662 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1662 = false ∨ valuation q 1666 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1663 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_right (literal (valuationOf q) (1663)) (literal (valuationOf q) (1667)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 3 (meaning1663 q) (meaning1667 q) hs
  change valuationOf q 1663 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1663 = false ∨ valuation q 1667 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1664 = false ∨ valuationOf q 1668 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_right (literal (valuationOf q) (1664)) (literal (valuationOf q) (1668)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 4 (meaning1664 q) (meaning1668 q) hs
  change valuationOf q 1664 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1664 = false ∨ valuation q 1668 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1665 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1654)) (literal (valuationOf q) (1665)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 1 (meaning1654 q) (meaning1665 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1665 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1666)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 1 1 (meaning1654 q) (meaning1661 q) (meaning1666 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1661 = false ∨ valuation q 1666 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1667)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 1 2 (meaning1654 q) (meaning1662 q) (meaning1667 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1662 = false ∨ valuation q 1667 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1668 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1668)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 1 3 (meaning1654 q) (meaning1663 q) (meaning1668 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1663 = false ∨ valuation q 1668 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1669 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1669)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 1 4 (meaning1654 q) (meaning1664 q) (meaning1669 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1664 = false ∨ valuation q 1669 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1666 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1655)) (literal (valuationOf q) (1666)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 2 (meaning1655 q) (meaning1666 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1666 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1667)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 2 1 (meaning1655 q) (meaning1661 q) (meaning1667 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1661 = false ∨ valuation q 1667 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1668 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1668)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 2 2 (meaning1655 q) (meaning1662 q) (meaning1668 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1662 = false ∨ valuation q 1668 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1669 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1669)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 2 3 (meaning1655 q) (meaning1663 q) (meaning1669 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1663 = false ∨ valuation q 1669 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1655 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1670 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1655)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1670)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 2 4 (meaning1655 q) (meaning1664 q) (meaning1670 q) hs
  change valuationOf q 1655 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1655 = false ∨ valuation q 1664 = false ∨ valuation q 1670 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1667 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_left (literal (valuationOf q) (1656)) (literal (valuationOf q) (1667)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 3 (meaning1656 q) (meaning1667 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1667 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1668 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1668)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 3 1 (meaning1656 q) (meaning1661 q) (meaning1668 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1661 = false ∨ valuation q 1668 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1669 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1662)) (literal (valuationOf q) (1669)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 3 2 (meaning1656 q) (meaning1662 q) (meaning1669 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1662 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1662 = false ∨ valuation q 1669 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1656 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1670 = true := by
  have hs : count1665 q = (countLit q [-79, -81, -82]) + (countLit q [-84, -85, -86, -88]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -82]) (l₂ := [-84, -85, -86, -88])
  have hm := merge_two (literal (valuationOf q) (1656)) (literal (valuationOf q) (1663)) (literal (valuationOf q) (1670)) (countLit q [-79, -81, -82]) (countLit q [-84, -85, -86, -88]) (count1665 q) 3 3 (meaning1656 q) (meaning1663 q) (meaning1670 q) hs
  change valuationOf q 1656 = false ∨ valuationOf q 1663 = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1656 = false ∨ valuation q 1663 = false ∨ valuation q 1670 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E258.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112258
