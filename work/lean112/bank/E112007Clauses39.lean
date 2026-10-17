import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1684)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 6 2 (meaning1614 q) (meaning1664 q) (meaning1684 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1664 = false ∨ valuation q 1684 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1685)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 6 3 (meaning1614 q) (meaning1665 q) (meaning1685 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1665 = false ∨ valuation q 1685 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1686)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 6 4 (meaning1614 q) (meaning1666 q) (meaning1686 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1666 = false ∨ valuation q 1686 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1687)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 6 5 (meaning1614 q) (meaning1667 q) (meaning1687 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1667 = false ∨ valuation q 1687 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1688 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1688)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 6 6 (meaning1614 q) (meaning1668 q) (meaning1688 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1668 = false ∨ valuation q 1688 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1686)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 7 3 (meaning1615 q) (meaning1665 q) (meaning1686 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1665 = false ∨ valuation q 1686 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1687)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 7 4 (meaning1615 q) (meaning1666 q) (meaning1687 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1666 = false ∨ valuation q 1687 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1688 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1688)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 7 5 (meaning1615 q) (meaning1667 q) (meaning1688 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1667 = false ∨ valuation q 1688 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1687)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 8 3 (meaning1616 q) (meaning1665 q) (meaning1687 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1665 = false ∨ valuation q 1687 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1688 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1688)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 8 4 (meaning1616 q) (meaning1666 q) (meaning1688 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1666 = false ∨ valuation q 1688 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1688 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1688)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 9 3 (meaning1617 q) (meaning1665 q) (meaning1688 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1665 = false ∨ valuation q 1688 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1556)) (literal (valuationOf q) (1688)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1693 q) 4 12 (meaning1556 q) (meaning1688 q) (meaning1708 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1688 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1688 = false ∨ valuation q 1708 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1687)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1693 q) 5 11 (meaning1557 q) (meaning1687 q) (meaning1708 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1687 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1687 = false ∨ valuation q 1708 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1686)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1693 q) 6 10 (meaning1558 q) (meaning1686 q) (meaning1708 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1686 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1686 = false ∨ valuation q 1708 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1685)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1693 q) 7 9 (meaning1559 q) (meaning1685 q) (meaning1708 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1685 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1685 = false ∨ valuation q 1708 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1684)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1693 q) 8 8 (meaning1560 q) (meaning1684 q) (meaning1708 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1684 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1684 = false ∨ valuation q 1708 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1683)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1693 q) 9 7 (meaning1561 q) (meaning1683 q) (meaning1708 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1683 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1683 = false ∨ valuation q 1708 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1562)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1693 q) 10 6 (meaning1562 q) (meaning1682 q) (meaning1708 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1682 = false ∨ valuation q 1708 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true := by
  have hs : count1693 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) + (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (l₂ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1563)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1708)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31, -34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90, -92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1693 q) 11 5 (meaning1563 q) (meaning1681 q) (meaning1708 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1708 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1681 = false ∨ valuation q 1708 = true := counterClause1267 (baseVal q)

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1708 = false := by
  rw [value1708]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1693 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 55 = false ∨ valuation q 73 = false := by
  rw [value6, value12, value55, value73]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (18 : Vertex) (82 : Vertex) (274 : Vertex) (338 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 18 = false ∨ valuation q 24 = false ∨ valuation q 28 = false := by
  rw [value14, value18, value24, value28]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (128 : Vertex) (132 : Vertex) (144 : Vertex) (148 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 26 = false ∨ valuation q 29 = false := by
  rw [value16, value21, value26, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (138 : Vertex) (146 : Vertex) (154 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 16 = false ∨ valuation q 21 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value16, value21, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (130 : Vertex) (138 : Vertex) (386 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 19 = false ∨ valuation q 82 = false ∨ valuation q 85 = false := by
  rw [value17, value19, value82, value85]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (131 : Vertex) (135 : Vertex) (387 : Vertex) (391 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 88 = false ∨ valuation q 98 = false := by
  rw [value21, value29, value88, value98]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (138 : Vertex) (154 : Vertex) (394 : Vertex) (410 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false ∨ valuation q 48 = false := by
  rw [value45, value46, value47, value48]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (216 : Vertex) (217 : Vertex) (218 : Vertex) (219 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 55 = false ∨ valuation q 56 = false := by
  rw [value50, value51, value55, value56]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (274 : Vertex) (275 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 51 = false ∨ valuation q 81 = false ∨ valuation q 82 = false := by
  rw [value50, value51, value81, value82]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (259 : Vertex) (386 : Vertex) (387 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 65 = false ∨ valuation q 70 = false := by
  rw [value50, value52, value65, value70]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (266 : Vertex) (322 : Vertex) (330 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 50 = false ∨ valuation q 52 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value50, value52, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (266 : Vertex) (386 : Vertex) (394 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 51 = false ∨ valuation q 56 = false ∨ valuation q 82 = false ∨ valuation q 92 = false := by
  rw [value51, value56, value82, value92]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (259 : Vertex) (275 : Vertex) (387 : Vertex) (403 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E007.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112007
