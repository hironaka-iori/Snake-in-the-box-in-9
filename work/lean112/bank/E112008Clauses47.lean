import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 2 8 (meaning1695 q) (meaning1764 q) (meaning1782 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1764 = false ∨ valuation q 1782 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1779 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1779)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 3 4 (meaning1696 q) (meaning1760 q) (meaning1779 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1760 = false ∨ valuation q 1779 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1780 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1780)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 3 5 (meaning1696 q) (meaning1761 q) (meaning1780 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1761 = false ∨ valuation q 1780 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 3 6 (meaning1696 q) (meaning1762 q) (meaning1781 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1762 = false ∨ valuation q 1781 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 3 7 (meaning1696 q) (meaning1763 q) (meaning1782 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1763 = false ∨ valuation q 1782 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 3 8 (meaning1696 q) (meaning1764 q) (meaning1783 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1764 = false ∨ valuation q 1783 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1765)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 3 9 (meaning1696 q) (meaning1765 q) (meaning1784 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1765 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1765 = false ∨ valuation q 1784 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1779 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1779)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 4 3 (meaning1697 q) (meaning1759 q) (meaning1779 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1759 = false ∨ valuation q 1779 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1780 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1780)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 4 4 (meaning1697 q) (meaning1760 q) (meaning1780 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1760 = false ∨ valuation q 1780 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 4 5 (meaning1697 q) (meaning1761 q) (meaning1781 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1761 = false ∨ valuation q 1781 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 4 6 (meaning1697 q) (meaning1762 q) (meaning1782 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1762 = false ∨ valuation q 1782 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 4 7 (meaning1697 q) (meaning1763 q) (meaning1783 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1763 = false ∨ valuation q 1783 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 4 8 (meaning1697 q) (meaning1764 q) (meaning1784 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1764 = false ∨ valuation q 1784 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1779 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1779)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 5 2 (meaning1698 q) (meaning1758 q) (meaning1779 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1758 = false ∨ valuation q 1779 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1780 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1780)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 5 3 (meaning1698 q) (meaning1759 q) (meaning1780 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1759 = false ∨ valuation q 1780 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 5 4 (meaning1698 q) (meaning1760 q) (meaning1781 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1760 = false ∨ valuation q 1781 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 5 5 (meaning1698 q) (meaning1761 q) (meaning1782 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1761 = false ∨ valuation q 1782 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 5 6 (meaning1698 q) (meaning1762 q) (meaning1783 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1762 = false ∨ valuation q 1783 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 5 7 (meaning1698 q) (meaning1763 q) (meaning1784 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1763 = false ∨ valuation q 1784 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1785)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 5 8 (meaning1698 q) (meaning1764 q) (meaning1785 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1764 = false ∨ valuation q 1785 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1780)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 6 2 (meaning1699 q) (meaning1758 q) (meaning1780 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1758 = false ∨ valuation q 1780 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 6 3 (meaning1699 q) (meaning1759 q) (meaning1781 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1759 = false ∨ valuation q 1781 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 6 4 (meaning1699 q) (meaning1760 q) (meaning1782 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1760 = false ∨ valuation q 1782 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 6 5 (meaning1699 q) (meaning1761 q) (meaning1783 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1761 = false ∨ valuation q 1783 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 6 6 (meaning1699 q) (meaning1762 q) (meaning1784 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1762 = false ∨ valuation q 1784 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1785)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 6 7 (meaning1699 q) (meaning1763 q) (meaning1785 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1763 = false ∨ valuation q 1785 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1786 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1764)) (literal (valuationOf q) (1786)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 6 8 (meaning1699 q) (meaning1764 q) (meaning1786 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1764 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1764 = false ∨ valuation q 1786 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1781 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 7 2 (meaning1700 q) (meaning1758 q) (meaning1781 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1758 = false ∨ valuation q 1781 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1782 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 7 3 (meaning1700 q) (meaning1759 q) (meaning1782 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1759 = false ∨ valuation q 1782 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1783 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 7 4 (meaning1700 q) (meaning1760 q) (meaning1783 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1760 = false ∨ valuation q 1783 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1784 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 7 5 (meaning1700 q) (meaning1761 q) (meaning1784 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1761 = false ∨ valuation q 1784 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1785 = true := by
  have hs : count1773 q = (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) + (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (l₂ := [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1785)) (countLit q [-60, -62, -63, -65, -66, -68, -71, -73, -74, -77, -80, -82, -83, -86, -89]) (countLit q [-90, -94, -97, -99, -100, -102, -103, -105, -107, -110, -112, -113, -116, -119, -121, -122]) (count1773 q) 7 6 (meaning1700 q) (meaning1762 q) (meaning1785 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1762 = false ∨ valuation q 1785 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E008.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112008
