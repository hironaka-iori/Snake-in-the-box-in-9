import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1728)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 9 (meaning1639 q) (meaning1709 q) (meaning1728 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1709 = false ∨ valuation q 1728 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1639)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1729)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 3 10 (meaning1639 q) (meaning1710 q) (meaning1729 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1710 = false ∨ valuation q 1729 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1725)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 5 (meaning1640 q) (meaning1705 q) (meaning1725 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1705 = false ∨ valuation q 1725 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1726)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 6 (meaning1640 q) (meaning1706 q) (meaning1726 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1706 = false ∨ valuation q 1726 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1727)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 7 (meaning1640 q) (meaning1707 q) (meaning1727 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1707 = false ∨ valuation q 1727 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1728)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 8 (meaning1640 q) (meaning1708 q) (meaning1728 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1708 = false ∨ valuation q 1728 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1729)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 9 (meaning1640 q) (meaning1709 q) (meaning1729 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1709 = false ∨ valuation q 1729 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1730)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 4 10 (meaning1640 q) (meaning1710 q) (meaning1730 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1710 = false ∨ valuation q 1730 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1724 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1724)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 3 (meaning1641 q) (meaning1703 q) (meaning1724 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1703 = false ∨ valuation q 1724 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1725)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 4 (meaning1641 q) (meaning1704 q) (meaning1725 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1704 = false ∨ valuation q 1725 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1726)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 5 (meaning1641 q) (meaning1705 q) (meaning1726 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1705 = false ∨ valuation q 1726 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1727)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 6 (meaning1641 q) (meaning1706 q) (meaning1727 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1706 = false ∨ valuation q 1727 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1728)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 7 (meaning1641 q) (meaning1707 q) (meaning1728 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1707 = false ∨ valuation q 1728 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1729)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 8 (meaning1641 q) (meaning1708 q) (meaning1729 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1708 = false ∨ valuation q 1729 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1730)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 9 (meaning1641 q) (meaning1709 q) (meaning1730 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1709 = false ∨ valuation q 1730 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1731 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1710)) (literal (valuationOf q) (1731)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 10 (meaning1641 q) (meaning1710 q) (meaning1731 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1710 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1710 = false ∨ valuation q 1731 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1726)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 4 (meaning1642 q) (meaning1704 q) (meaning1726 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1704 = false ∨ valuation q 1726 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1727)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 5 (meaning1642 q) (meaning1705 q) (meaning1727 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1705 = false ∨ valuation q 1727 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1728)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 6 (meaning1642 q) (meaning1706 q) (meaning1728 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1706 = false ∨ valuation q 1728 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1729)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 7 (meaning1642 q) (meaning1707 q) (meaning1729 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1707 = false ∨ valuation q 1729 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1730)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 8 (meaning1642 q) (meaning1708 q) (meaning1730 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1708 = false ∨ valuation q 1730 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1731 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1709)) (literal (valuationOf q) (1731)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 9 (meaning1642 q) (meaning1709 q) (meaning1731 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1709 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1709 = false ∨ valuation q 1731 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1726)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 3 (meaning1643 q) (meaning1703 q) (meaning1726 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1703 = false ∨ valuation q 1726 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1727)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 4 (meaning1643 q) (meaning1704 q) (meaning1727 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1704 = false ∨ valuation q 1727 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1728)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 5 (meaning1643 q) (meaning1705 q) (meaning1728 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1705 = false ∨ valuation q 1728 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1729)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 6 (meaning1643 q) (meaning1706 q) (meaning1729 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1706 = false ∨ valuation q 1729 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1730)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 7 (meaning1643 q) (meaning1707 q) (meaning1730 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1707 = false ∨ valuation q 1730 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1731 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1731)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 8 (meaning1643 q) (meaning1708 q) (meaning1731 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1708 = false ∨ valuation q 1731 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1728)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 4 (meaning1644 q) (meaning1704 q) (meaning1728 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1704 = false ∨ valuation q 1728 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1729)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 5 (meaning1644 q) (meaning1705 q) (meaning1729 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1705 = false ∨ valuation q 1729 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1730)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 6 (meaning1644 q) (meaning1706 q) (meaning1730 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1706 = false ∨ valuation q 1730 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1731 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1731)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 7 (meaning1644 q) (meaning1707 q) (meaning1731 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1707 = false ∨ valuation q 1731 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E026.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112026
