import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -94, -97, -98, -102, -104]) + (countLit q [-105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94, -97, -98, -102, -104]) (l₂ := [-105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1667)) (countLit q [-92, -93, -94, -97, -98, -102, -104]) (countLit q [-105, -106, -109, -111, -113, -115, -117]) (count1663 q) 4 1 (meaning1639 q) (meaning1656 q) (meaning1667 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1656 = false ∨ valuation q 1667 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -94, -97, -98, -102, -104]) + (countLit q [-105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94, -97, -98, -102, -104]) (l₂ := [-105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1668)) (countLit q [-92, -93, -94, -97, -98, -102, -104]) (countLit q [-105, -106, -109, -111, -113, -115, -117]) (count1663 q) 4 2 (meaning1639 q) (meaning1657 q) (meaning1668 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1657 = false ∨ valuation q 1668 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1669 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -94, -97, -98, -102, -104]) + (countLit q [-105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94, -97, -98, -102, -104]) (l₂ := [-105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1658)) (literal (valuationOf q) (1669)) (countLit q [-92, -93, -94, -97, -98, -102, -104]) (countLit q [-105, -106, -109, -111, -113, -115, -117]) (count1663 q) 4 3 (meaning1639 q) (meaning1658 q) (meaning1669 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1658 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1658 = false ∨ valuation q 1669 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -94, -97, -98, -102, -104]) + (countLit q [-105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94, -97, -98, -102, -104]) (l₂ := [-105, -106, -109, -111, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1640)) (literal (valuationOf q) (1667)) (countLit q [-92, -93, -94, -97, -98, -102, -104]) (countLit q [-105, -106, -109, -111, -113, -115, -117]) (count1663 q) 5 (meaning1640 q) (meaning1667 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1667 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -94, -97, -98, -102, -104]) + (countLit q [-105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94, -97, -98, -102, -104]) (l₂ := [-105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1668)) (countLit q [-92, -93, -94, -97, -98, -102, -104]) (countLit q [-105, -106, -109, -111, -113, -115, -117]) (count1663 q) 5 1 (meaning1640 q) (meaning1656 q) (meaning1668 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1656 = false ∨ valuation q 1668 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1669 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -94, -97, -98, -102, -104]) + (countLit q [-105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94, -97, -98, -102, -104]) (l₂ := [-105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1657)) (literal (valuationOf q) (1669)) (countLit q [-92, -93, -94, -97, -98, -102, -104]) (countLit q [-105, -106, -109, -111, -113, -115, -117]) (count1663 q) 5 2 (meaning1640 q) (meaning1657 q) (meaning1669 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1657 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1657 = false ∨ valuation q 1669 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -94, -97, -98, -102, -104]) + (countLit q [-105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94, -97, -98, -102, -104]) (l₂ := [-105, -106, -109, -111, -113, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1641)) (literal (valuationOf q) (1668)) (countLit q [-92, -93, -94, -97, -98, -102, -104]) (countLit q [-105, -106, -109, -111, -113, -115, -117]) (count1663 q) 6 (meaning1641 q) (meaning1668 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1668 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1669 = true := by
  have hs : count1663 q = (countLit q [-92, -93, -94, -97, -98, -102, -104]) + (countLit q [-105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -94, -97, -98, -102, -104]) (l₂ := [-105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1656)) (literal (valuationOf q) (1669)) (countLit q [-92, -93, -94, -97, -98, -102, -104]) (countLit q [-105, -106, -109, -111, -113, -115, -117]) (count1663 q) 6 1 (meaning1641 q) (meaning1656 q) (meaning1669 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1656 = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1656 = false ∨ valuation q 1669 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1682 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1682)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 1 5 (meaning1609 q) (meaning1667 q) (meaning1682 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1667 = false ∨ valuation q 1682 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1609 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1609)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1683)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 1 6 (meaning1609 q) (meaning1668 q) (meaning1683 q) hs
  change valuationOf q 1609 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1609 = false ∨ valuation q 1668 = false ∨ valuation q 1683 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1681 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1681)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 2 3 (meaning1610 q) (meaning1665 q) (meaning1681 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1665 = false ∨ valuation q 1681 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1682 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1682)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 2 4 (meaning1610 q) (meaning1666 q) (meaning1682 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1666 = false ∨ valuation q 1682 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1683)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 2 5 (meaning1610 q) (meaning1667 q) (meaning1683 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1667 = false ∨ valuation q 1683 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1684)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 2 6 (meaning1610 q) (meaning1668 q) (meaning1684 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1668 = false ∨ valuation q 1684 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1610)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1685)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 2 7 (meaning1610 q) (meaning1669 q) (meaning1685 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1669 = false ∨ valuation q 1685 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1682 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1682)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 3 3 (meaning1611 q) (meaning1665 q) (meaning1682 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1665 = false ∨ valuation q 1682 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1683)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 3 4 (meaning1611 q) (meaning1666 q) (meaning1683 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1666 = false ∨ valuation q 1683 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1684)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 3 5 (meaning1611 q) (meaning1667 q) (meaning1684 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1667 = false ∨ valuation q 1684 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1685)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 3 6 (meaning1611 q) (meaning1668 q) (meaning1685 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1668 = false ∨ valuation q 1685 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1611)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1686)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 3 7 (meaning1611 q) (meaning1669 q) (meaning1686 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1669 = false ∨ valuation q 1686 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1682 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1682)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 4 2 (meaning1612 q) (meaning1664 q) (meaning1682 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1664 = false ∨ valuation q 1682 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1683)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 4 3 (meaning1612 q) (meaning1665 q) (meaning1683 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1665 = false ∨ valuation q 1683 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1684)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 4 4 (meaning1612 q) (meaning1666 q) (meaning1684 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1666 = false ∨ valuation q 1684 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1685)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 4 5 (meaning1612 q) (meaning1667 q) (meaning1685 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1667 = false ∨ valuation q 1685 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1686)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 4 6 (meaning1612 q) (meaning1668 q) (meaning1686 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1668 = false ∨ valuation q 1686 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1687)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 4 7 (meaning1612 q) (meaning1669 q) (meaning1687 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1669 = false ∨ valuation q 1687 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1683 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1664)) (literal (valuationOf q) (1683)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 5 2 (meaning1613 q) (meaning1664 q) (meaning1683 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1664 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1664 = false ∨ valuation q 1683 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1684 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1665)) (literal (valuationOf q) (1684)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 5 3 (meaning1613 q) (meaning1665 q) (meaning1684 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1665 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1665 = false ∨ valuation q 1684 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1685 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1666)) (literal (valuationOf q) (1685)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 5 4 (meaning1613 q) (meaning1666 q) (meaning1685 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1666 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1666 = false ∨ valuation q 1685 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1686 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1667)) (literal (valuationOf q) (1686)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 5 5 (meaning1613 q) (meaning1667 q) (meaning1686 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1667 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1667 = false ∨ valuation q 1686 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1687 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1668)) (literal (valuationOf q) (1687)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 5 6 (meaning1613 q) (meaning1668 q) (meaning1687 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1668 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1668 = false ∨ valuation q 1687 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1688 = true := by
  have hs : count1677 q = (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) + (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (l₂ := [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1688)) (countLit q [-61, -64, -65, -67, -68, -72, -74, -76, -77, -81, -83, -85, -86, -90]) (countLit q [-92, -93, -94, -97, -98, -102, -104, -105, -106, -109, -111, -113, -115, -117]) (count1677 q) 5 7 (meaning1613 q) (meaning1669 q) (meaning1688 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1669 = false ∨ valuation q 1688 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E007.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112007
