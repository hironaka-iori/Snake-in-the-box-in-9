import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1781 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 5 6 (meaning1695 q) (meaning1760 q) (meaning1781 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1760 = false ∨ valuation q 1781 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 5 7 (meaning1695 q) (meaning1761 q) (meaning1782 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1761 = false ∨ valuation q 1782 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 5 8 (meaning1695 q) (meaning1762 q) (meaning1783 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1762 = false ∨ valuation q 1783 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1695 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1784 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1695)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 5 9 (meaning1695 q) (meaning1763 q) (meaning1784 q) hs
  change valuationOf q 1695 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1695 = false ∨ valuation q 1763 = false ∨ valuation q 1784 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1780)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 6 4 (meaning1696 q) (meaning1758 q) (meaning1780 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1758 = false ∨ valuation q 1780 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1781 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 6 5 (meaning1696 q) (meaning1759 q) (meaning1781 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1759 = false ∨ valuation q 1781 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 6 6 (meaning1696 q) (meaning1760 q) (meaning1782 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1760 = false ∨ valuation q 1782 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 6 7 (meaning1696 q) (meaning1761 q) (meaning1783 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1761 = false ∨ valuation q 1783 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1784 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 6 8 (meaning1696 q) (meaning1762 q) (meaning1784 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1762 = false ∨ valuation q 1784 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1696 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1785 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1696)) (literal (valuationOf q) (1763)) (literal (valuationOf q) (1785)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 6 9 (meaning1696 q) (meaning1763 q) (meaning1785 q) hs
  change valuationOf q 1696 = false ∨ valuationOf q 1763 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1696 = false ∨ valuation q 1763 = false ∨ valuation q 1785 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1780 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1780)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 7 3 (meaning1697 q) (meaning1757 q) (meaning1780 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1757 = false ∨ valuation q 1780 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1781 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 7 4 (meaning1697 q) (meaning1758 q) (meaning1781 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1758 = false ∨ valuation q 1781 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 7 5 (meaning1697 q) (meaning1759 q) (meaning1782 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1759 = false ∨ valuation q 1782 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 7 6 (meaning1697 q) (meaning1760 q) (meaning1783 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1760 = false ∨ valuation q 1783 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1784 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 7 7 (meaning1697 q) (meaning1761 q) (meaning1784 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1761 = false ∨ valuation q 1784 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1697 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1785 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1697)) (literal (valuationOf q) (1762)) (literal (valuationOf q) (1785)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 7 8 (meaning1697 q) (meaning1762 q) (meaning1785 q) hs
  change valuationOf q 1697 = false ∨ valuationOf q 1762 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1697 = false ∨ valuation q 1762 = false ∨ valuation q 1785 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1781 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1781)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 8 3 (meaning1698 q) (meaning1757 q) (meaning1781 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1781 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1757 = false ∨ valuation q 1781 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 8 4 (meaning1698 q) (meaning1758 q) (meaning1782 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1758 = false ∨ valuation q 1782 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 8 5 (meaning1698 q) (meaning1759 q) (meaning1783 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1759 = false ∨ valuation q 1783 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1784 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 8 6 (meaning1698 q) (meaning1760 q) (meaning1784 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1760 = false ∨ valuation q 1784 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1698 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1785 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1698)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1785)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 8 7 (meaning1698 q) (meaning1761 q) (meaning1785 q) hs
  change valuationOf q 1698 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1698 = false ∨ valuation q 1761 = false ∨ valuation q 1785 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1782 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1782)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 9 3 (meaning1699 q) (meaning1757 q) (meaning1782 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1782 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1757 = false ∨ valuation q 1782 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1783 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1783)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 9 4 (meaning1699 q) (meaning1758 q) (meaning1783 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1783 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1758 = false ∨ valuation q 1783 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1784 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 9 5 (meaning1699 q) (meaning1759 q) (meaning1784 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1759 = false ∨ valuation q 1784 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1785 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1760)) (literal (valuationOf q) (1785)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 9 6 (meaning1699 q) (meaning1760 q) (meaning1785 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1760 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1760 = false ∨ valuation q 1785 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1699 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1786 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1699)) (literal (valuationOf q) (1761)) (literal (valuationOf q) (1786)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 9 7 (meaning1699 q) (meaning1761 q) (meaning1786 q) hs
  change valuationOf q 1699 = false ∨ valuationOf q 1761 = false ∨ valuationOf q 1786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1699 = false ∨ valuation q 1761 = false ∨ valuation q 1786 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1784 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1784)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 10 4 (meaning1700 q) (meaning1758 q) (meaning1784 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1784 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1758 = false ∨ valuation q 1784 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1700 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1785 = true := by
  have hs : count1771 q = (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) + (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (l₂ := [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1700)) (literal (valuationOf q) (1759)) (literal (valuationOf q) (1785)) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92]) (countLit q [-94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1771 q) 10 5 (meaning1700 q) (meaning1759 q) (meaning1785 q) hs
  change valuationOf q 1700 = false ∨ valuationOf q 1759 = false ∨ valuationOf q 1785 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1700 = false ∨ valuation q 1759 = false ∨ valuation q 1785 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1626 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) + (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (l₂ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1626)) (literal (valuationOf q) (1786)) (literal (valuationOf q) (1816)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1794 q) 7 16 (meaning1626 q) (meaning1786 q) (meaning1816 q) hs
  change valuationOf q 1626 = false ∨ valuationOf q 1786 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1626 = false ∨ valuation q 1786 = false ∨ valuation q 1816 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1627 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) + (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (l₂ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1627)) (literal (valuationOf q) (1785)) (literal (valuationOf q) (1816)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1794 q) 8 15 (meaning1627 q) (meaning1785 q) (meaning1816 q) hs
  change valuationOf q 1627 = false ∨ valuationOf q 1785 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1627 = false ∨ valuation q 1785 = false ∨ valuation q 1816 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1628 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) + (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (l₂ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1628)) (literal (valuationOf q) (1784)) (literal (valuationOf q) (1816)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1794 q) 9 14 (meaning1628 q) (meaning1784 q) (meaning1816 q) hs
  change valuationOf q 1628 = false ∨ valuationOf q 1784 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1628 = false ∨ valuation q 1784 = false ∨ valuation q 1816 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true := by
  have hs : count1794 q = (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) + (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (l₂ := [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1783)) (literal (valuationOf q) (1816)) (countLit q [-1, -3, -5, -6, -8, -10, -13, -15, -16, -17, -19, -22, -25, -26, -28, -31, -33, -34, -36, -37, -41, -42, -43, -44, -48, -50, -51, -52, -54, -57, -59]) (countLit q [-60, -62, -65, -66, -69, -70, -71, -75, -76, -78, -81, -83, -84, -87, -91, -92, -94, -97, -98, -100, -101, -102, -105, -107, -109, -112, -113, -114, -117, -119, -122, -123]) (count1794 q) 10 13 (meaning1629 q) (meaning1783 q) (meaning1816 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1783 = false ∨ valuationOf q 1816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1783 = false ∨ valuation q 1816 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E186.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112186
