import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1786)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 7 7 (meaning1700 q) (meaning1763 q) (meaning1786 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1763 = false ∨ valuation q 1786 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 8 2 (meaning1701 q) (meaning1758 q) (meaning1782 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1758 = false ∨ valuation q 1782 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 8 3 (meaning1701 q) (meaning1759 q) (meaning1783 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1759 = false ∨ valuation q 1783 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 8 4 (meaning1701 q) (meaning1760 q) (meaning1784 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1760 = false ∨ valuation q 1784 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 9 2 (meaning1702 q) (meaning1758 q) (meaning1783 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1758 = false ∨ valuation q 1783 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1635 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) + (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (l₂ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1635)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1816)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1795 q) 8 14 (meaning1635 q) (meaning1786 q) (meaning1816 q) hs
  change valuationOf q 1635 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1635 = false ∨ valuation q 1786 = false ∨ valuation q 1816 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) + (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (l₂ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1816)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1795 q) 9 13 (meaning1636 q) (meaning1785 q) (meaning1816 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1785 = false ∨ valuation q 1816 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) + (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (l₂ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1816)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1795 q) 10 12 (meaning1637 q) (meaning1784 q) (meaning1816 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1784 = false ∨ valuation q 1816 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) + (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (l₂ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1638)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1816)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1795 q) 11 11 (meaning1638 q) (meaning1783 q) (meaning1816 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1783 = false ∨ valuation q 1816 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) + (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (l₂ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1782)) (literal (valuationOf q) (1816)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1795 q) 12 10 (meaning1639 q) (meaning1782 q) (meaning1816 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1782 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1782 = false ∨ valuation q 1816 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) + (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (l₂ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1781)) (literal (valuationOf q) (1816)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1795 q) 13 9 (meaning1640 q) (meaning1781 q) (meaning1816 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1781 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1781 = false ∨ valuation q 1816 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1780 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) + (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (l₂ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1780)) (literal (valuationOf q) (1816)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1795 q) 14 8 (meaning1641 q) (meaning1780 q) (meaning1816 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1780 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1780 = false ∨ valuation q 1816 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1816 = true := by
  have hs : count1795 q = (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) + (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (l₂ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1779)) (literal (valuationOf q) (1816)) (countLit q [-3, -5, -6, -8, -10, -12, -13, -14, -17, -19, -20, -21, -24, -25, -26, -28, -29, -33, -34, -35, -38, -40, -42, -44, -45, -48, -51, -53, -54, -56, -57]) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89, -90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1795 q) 15 7 (meaning1642 q) (meaning1779 q) (meaning1816 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1779 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1779 = false ∨ valuation q 1816 = true := counterClause1549 (baseVal q)

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1816 = false := by
  rw [value1816]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1795 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value1, value3, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (33 : Vertex) (35 : Vertex) (49 : Vertex) (51 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 5 = false ∨ valuation q 71 = false ∨ valuation q 75 = false := by
  rw [value1, value5, value71, value75]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (33 : Vertex) (41 : Vertex) (289 : Vertex) (297 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 33 = false ∨ valuation q 71 = false ∨ valuation q 87 = false := by
  rw [value1, value33, value71, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (33 : Vertex) (161 : Vertex) (289 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 19 = false ∨ valuation q 23 = false := by
  rw [value2, value6, value19, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (34 : Vertex) (42 : Vertex) (98 : Vertex) (106 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 6 = false ∨ valuation q 34 = false ∨ valuation q 39 = false := by
  rw [value2, value6, value34, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (34 : Vertex) (42 : Vertex) (162 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 2 = false ∨ valuation q 19 = false ∨ valuation q 34 = false ∨ valuation q 52 = false := by
  rw [value2, value19, value34, value52]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (34 : Vertex) (98 : Vertex) (162 : Vertex) (226 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 15 = false ∨ valuation q 23 = false ∨ valuation q 29 = false := by
  rw [value6, value15, value23, value29]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (42 : Vertex) (58 : Vertex) (106 : Vertex) (122 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 23 = false ∨ valuation q 39 = false ∨ valuation q 57 = false := by
  rw [value6, value23, value39, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (42 : Vertex) (106 : Vertex) (170 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 9 = false ∨ valuation q 12 = false ∨ valuation q 14 = false ∨ valuation q 16 = false := by
  rw [value9, value12, value14, value16]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (48 : Vertex) (52 : Vertex) (56 : Vertex) (60 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 15 = false ∨ valuation q 16 = false ∨ valuation q 17 = false := by
  rw [value14, value15, value16, value17]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (56 : Vertex) (58 : Vertex) (60 : Vertex) (62 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 19 = false ∨ valuation q 23 = false ∨ valuation q 52 = false ∨ valuation q 57 = false := by
  rw [value19, value23, value52, value57]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (98 : Vertex) (106 : Vertex) (226 : Vertex) (234 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 35 = false ∨ valuation q 36 = false := by
  rw [value32, value33, value35, value36]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (164 : Vertex) (165 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 33 = false ∨ valuation q 86 = false ∨ valuation q 87 = false := by
  rw [value32, value33, value86, value87]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (416 : Vertex) (417 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 37 = false := by
  rw [value32, value34, value35, value37]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (162 : Vertex) (164 : Vertex) (166 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 34 = false ∨ valuation q 38 = false ∨ valuation q 39 = false := by
  rw [value32, value34, value38, value39]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (162 : Vertex) (168 : Vertex) (170 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 35 = false ∨ valuation q 38 = false ∨ valuation q 41 = false := by
  rw [value32, value35, value38, value41]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (164 : Vertex) (168 : Vertex) (172 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 33 = false ∨ valuation q 36 = false ∨ valuation q 87 = false ∨ valuation q 90 = false := by
  rw [value33, value36, value87, value90]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (161 : Vertex) (165 : Vertex) (417 : Vertex) (421 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 37 = false ∨ valuation q 43 = false ∨ valuation q 45 = false := by
  rw [value34, value37, value43, value45]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (166 : Vertex) (178 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E008.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112008
