import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) + (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (l₂ := [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1782)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1771 q) 6 6 (meaning1696 q) (meaning1760 q) (meaning1782 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1760 = false ∨ valuation q 1782 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) + (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (l₂ := [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1783)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1771 q) 6 7 (meaning1696 q) (meaning1761 q) (meaning1783 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1761 = false ∨ valuation q 1783 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1781 = true := by
  have hs : count1771 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) + (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (l₂ := [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1781)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1771 q) 7 4 (meaning1697 q) (meaning1758 q) (meaning1781 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1758 = false ∨ valuation q 1781 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) + (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (l₂ := [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1782)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1771 q) 7 5 (meaning1697 q) (meaning1759 q) (meaning1782 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1759 = false ∨ valuation q 1782 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) + (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (l₂ := [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1783)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1771 q) 7 6 (meaning1697 q) (meaning1760 q) (meaning1783 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1760 = false ∨ valuation q 1783 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) + (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (l₂ := [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1782)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1771 q) 8 4 (meaning1698 q) (meaning1758 q) (meaning1782 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1758 = false ∨ valuation q 1782 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) + (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (l₂ := [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1783)) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91]) (countLit q [-92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1771 q) 9 4 (meaning1699 q) (meaning1758 q) (meaning1783 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1758 = false ∨ valuation q 1783 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) + (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (l₂ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1816)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1794 q) 10 13 (meaning1629 q) (meaning1783 q) (meaning1816 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1783 = false ∨ valuation q 1816 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) + (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (l₂ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1782)) (literal (valuationOf q) (1816)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1794 q) 11 12 (meaning1630 q) (meaning1782 q) (meaning1816 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1782 = false ∨ valuation q 1816 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) + (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (l₂ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1781)) (literal (valuationOf q) (1816)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1794 q) 12 11 (meaning1631 q) (meaning1781 q) (meaning1816 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1781 = false ∨ valuation q 1816 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1780 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) + (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (l₂ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1780)) (literal (valuationOf q) (1816)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1794 q) 13 10 (meaning1632 q) (meaning1780 q) (meaning1816 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1780 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1780 = false ∨ valuation q 1816 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) + (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (l₂ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1633)) (literal (valuationOf q) (1779)) (literal (valuationOf q) (1816)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1794 q) 14 9 (meaning1633 q) (meaning1779 q) (meaning1816 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1779 = false ∨ valuation q 1816 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1634 = false ∨ valuationOf q 1778 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) + (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (l₂ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1634)) (literal (valuationOf q) (1778)) (literal (valuationOf q) (1816)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1794 q) 15 8 (meaning1634 q) (meaning1778 q) (meaning1816 q) hs
  change valuationOf q 1634 = false ∨ valuationOf q 1778 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1634 = false ∨ valuation q 1778 = false ∨ valuation q 1816 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1777 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) + (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (l₂ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1777)) (literal (valuationOf q) (1816)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1794 q) 16 7 (meaning1635 q) (meaning1777 q) (meaning1816 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1777 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1777 = false ∨ valuation q 1816 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1776 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) + (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (l₂ := [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1776)) (literal (valuationOf q) (1816)) (countLit q [-2, -3, -5, -6, -8, -9, -12, -13, -15, -16, -18, -21, -22, -24, -27, -29, -30, -31, -34, -35, -37, -38, -40, -42, -45, -47, -48, -49, -53, -54, -56]) (countLit q [-58, -60, -61, -65, -66, -68, -69, -73, -75, -76, -78, -80, -83, -84, -88, -91, -92, -94, -96, -99, -100, -103, -104, -106, -107, -109, -111, -113, -116, -118, -121, -124]) (count1794 q) 17 6 (meaning1636 q) (meaning1776 q) (meaning1816 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1776 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1776 = false ∨ valuation q 1816 = true := counterClause1551 (baseVal q)

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1816 = false := by
  rw [value1816]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1794 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 5 = false ∨ valuation q 10 = false ∨ valuation q 19 = false ∨ valuation q 29 = false := by
  rw [value5, value10, value19, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (41 : Vertex) (57 : Vertex) (105 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 25 = false ∨ valuation q 29 = false := by
  rw [value8, value10, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (57 : Vertex) (113 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 43 = false ∨ valuation q 47 = false := by
  rw [value8, value10, value43, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (57 : Vertex) (177 : Vertex) (185 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 25 = false ∨ valuation q 43 = false ∨ valuation q 60 = false := by
  rw [value8, value25, value43, value60]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (49 : Vertex) (113 : Vertex) (177 : Vertex) (241 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 29 = false ∨ valuation q 47 = false ∨ valuation q 67 = false := by
  rw [value10, value29, value47, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (57 : Vertex) (121 : Vertex) (185 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value14, value15, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (97 : Vertex) (98 : Vertex) (99 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value14, value15, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (97 : Vertex) (112 : Vertex) (113 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 16 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value14, value16, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (96 : Vertex) (98 : Vertex) (112 : Vertex) (114 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 25 = false ∨ valuation q 29 = false := by
  rw [value15, value19, value25, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (97 : Vertex) (105 : Vertex) (113 : Vertex) (121 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value15, value19, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (97 : Vertex) (105 : Vertex) (353 : Vertex) (361 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value20, value21, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (108 : Vertex) (109 : Vertex) (110 : Vertex) (111 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 22 = false ∨ valuation q 31 = false ∨ valuation q 32 = false := by
  rw [value20, value22, value31, value32]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (108 : Vertex) (110 : Vertex) (124 : Vertex) (126 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 27 = false ∨ valuation q 60 = false ∨ valuation q 62 = false := by
  rw [value25, value27, value60, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (113 : Vertex) (115 : Vertex) (241 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 25 = false ∨ valuation q 29 = false ∨ valuation q 60 = false ∨ valuation q 67 = false := by
  rw [value25, value29, value60, value67]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (113 : Vertex) (121 : Vertex) (241 : Vertex) (249 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 61 = false ∨ valuation q 62 = false := by
  rw [value26, value27, value61, value62]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (114 : Vertex) (115 : Vertex) (242 : Vertex) (243 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 26 = false ∨ valuation q 27 = false ∨ valuation q 78 = false ∨ valuation q 79 = false := by
  rw [value26, value27, value78, value79]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (114 : Vertex) (115 : Vertex) (370 : Vertex) (371 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E020.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112020
