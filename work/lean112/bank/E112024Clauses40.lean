import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec40 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1281 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1725)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 4 (meaning1641 q) (meaning1704 q) (meaning1725 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1281 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1704 = false ∨ valuation q 1725 = true := counterClause1281 (baseVal q)

theorem counterClause1282 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1726)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 5 (meaning1641 q) (meaning1705 q) (meaning1726 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1282 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1705 = false ∨ valuation q 1726 = true := counterClause1282 (baseVal q)

theorem counterClause1283 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1727)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 6 (meaning1641 q) (meaning1706 q) (meaning1727 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1283 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1706 = false ∨ valuation q 1727 = true := counterClause1283 (baseVal q)

theorem counterClause1284 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1728)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 7 (meaning1641 q) (meaning1707 q) (meaning1728 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1284 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1707 = false ∨ valuation q 1728 = true := counterClause1284 (baseVal q)

theorem counterClause1285 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1729)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 5 8 (meaning1641 q) (meaning1708 q) (meaning1729 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1285 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1708 = false ∨ valuation q 1729 = true := counterClause1285 (baseVal q)

theorem counterClause1286 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1724 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1702)) (literal (valuationOf q) (1724)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 2 (meaning1642 q) (meaning1702 q) (meaning1724 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1724 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1286 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1702 = false ∨ valuation q 1724 = true := counterClause1286 (baseVal q)

theorem counterClause1287 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1725)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 3 (meaning1642 q) (meaning1703 q) (meaning1725 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1287 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1703 = false ∨ valuation q 1725 = true := counterClause1287 (baseVal q)

theorem counterClause1288 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1726 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1726)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 4 (meaning1642 q) (meaning1704 q) (meaning1726 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1726 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1288 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1704 = false ∨ valuation q 1726 = true := counterClause1288 (baseVal q)

theorem counterClause1289 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1727)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 5 (meaning1642 q) (meaning1705 q) (meaning1727 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1289 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1705 = false ∨ valuation q 1727 = true := counterClause1289 (baseVal q)

theorem counterClause1290 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1728)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 6 (meaning1642 q) (meaning1706 q) (meaning1728 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1290 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1706 = false ∨ valuation q 1728 = true := counterClause1290 (baseVal q)

theorem counterClause1291 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1729)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 7 (meaning1642 q) (meaning1707 q) (meaning1729 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1291 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1707 = false ∨ valuation q 1729 = true := counterClause1291 (baseVal q)

theorem counterClause1292 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1730)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 6 8 (meaning1642 q) (meaning1708 q) (meaning1730 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1292 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1708 = false ∨ valuation q 1730 = true := counterClause1292 (baseVal q)

theorem counterClause1293 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1702)) (literal (valuationOf q) (1725)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 2 (meaning1643 q) (meaning1702 q) (meaning1725 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1702 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1293 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1702 = false ∨ valuation q 1725 = true := counterClause1293 (baseVal q)

theorem counterClause1294 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1727)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 4 (meaning1643 q) (meaning1704 q) (meaning1727 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1294 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1704 = false ∨ valuation q 1727 = true := counterClause1294 (baseVal q)

theorem counterClause1295 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1728)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 5 (meaning1643 q) (meaning1705 q) (meaning1728 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1295 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1705 = false ∨ valuation q 1728 = true := counterClause1295 (baseVal q)

theorem counterClause1296 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1729)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 6 (meaning1643 q) (meaning1706 q) (meaning1729 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1296 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1706 = false ∨ valuation q 1729 = true := counterClause1296 (baseVal q)

theorem counterClause1297 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1730)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 7 (meaning1643 q) (meaning1707 q) (meaning1730 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1297 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1707 = false ∨ valuation q 1730 = true := counterClause1297 (baseVal q)

theorem counterClause1298 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1731 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1708)) (literal (valuationOf q) (1731)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 7 8 (meaning1643 q) (meaning1708 q) (meaning1731 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1708 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1298 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1708 = false ∨ valuation q 1731 = true := counterClause1298 (baseVal q)

theorem counterClause1299 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1725 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1701)) (literal (valuationOf q) (1725)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 1 (meaning1644 q) (meaning1701 q) (meaning1725 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1701 = false ∨ valuationOf q 1725 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1299 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1701 = false ∨ valuation q 1725 = true := counterClause1299 (baseVal q)

theorem counterClause1300 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1727 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1727)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 3 (meaning1644 q) (meaning1703 q) (meaning1727 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1727 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1300 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1703 = false ∨ valuation q 1727 = true := counterClause1300 (baseVal q)

theorem counterClause1301 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1728)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 4 (meaning1644 q) (meaning1704 q) (meaning1728 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1301 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1704 = false ∨ valuation q 1728 = true := counterClause1301 (baseVal q)

theorem counterClause1302 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1729)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 5 (meaning1644 q) (meaning1705 q) (meaning1729 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1302 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1705 = false ∨ valuation q 1729 = true := counterClause1302 (baseVal q)

theorem counterClause1303 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1730)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 6 (meaning1644 q) (meaning1706 q) (meaning1730 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1303 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1706 = false ∨ valuation q 1730 = true := counterClause1303 (baseVal q)

theorem counterClause1304 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1731 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1707)) (literal (valuationOf q) (1731)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 8 7 (meaning1644 q) (meaning1707 q) (meaning1731 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1707 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1304 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1707 = false ∨ valuation q 1731 = true := counterClause1304 (baseVal q)

theorem counterClause1305 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1728 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1703)) (literal (valuationOf q) (1728)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 9 3 (meaning1645 q) (meaning1703 q) (meaning1728 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1703 = false ∨ valuationOf q 1728 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1305 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1703 = false ∨ valuation q 1728 = true := counterClause1305 (baseVal q)

theorem counterClause1306 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1729)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 9 4 (meaning1645 q) (meaning1704 q) (meaning1729 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1306 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1704 = false ∨ valuation q 1729 = true := counterClause1306 (baseVal q)

theorem counterClause1307 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1730)) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 9 5 (meaning1645 q) (meaning1705 q) (meaning1730 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1307 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1705 = false ∨ valuation q 1730 = true := counterClause1307 (baseVal q)

theorem counterClause1308 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) + (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (l₂ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 8 15 (meaning1573 q) (meaning1731 q) (meaning1762 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1308 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1731 = false ∨ valuation q 1762 = true := counterClause1308 (baseVal q)

theorem counterClause1309 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) + (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (l₂ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1730)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 9 14 (meaning1574 q) (meaning1730 q) (meaning1762 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1309 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1730 = false ∨ valuation q 1762 = true := counterClause1309 (baseVal q)

theorem counterClause1310 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) + (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (l₂ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1729)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 10 13 (meaning1575 q) (meaning1729 q) (meaning1762 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1310 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1729 = false ∨ valuation q 1762 = true := counterClause1310 (baseVal q)

theorem counterClause1311 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) + (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (l₂ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1728)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 11 12 (meaning1576 q) (meaning1728 q) (meaning1762 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1311 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1728 = false ∨ valuation q 1762 = true := counterClause1311 (baseVal q)

theorem counterClause1312 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) + (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (l₂ := [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1727)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -53, -54, -55, -56]) (countLit q [-58, -61, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 12 11 (meaning1577 q) (meaning1727 q) (meaning1762 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1312 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1727 = false ∨ valuation q 1762 = true := counterClause1312 (baseVal q)

theorem block40 (q : Snake 81) (h : Conditions q) : B112E024.Block40 (valuation q) :=
  ⟨clause1281 q h, clause1282 q h, clause1283 q h, clause1284 q h, clause1285 q h, clause1286 q h, clause1287 q h, clause1288 q h, clause1289 q h, clause1290 q h, clause1291 q h, clause1292 q h, clause1293 q h, clause1294 q h, clause1295 q h, clause1296 q h, clause1297 q h, clause1298 q h, clause1299 q h, clause1300 q h, clause1301 q h, clause1302 q h, clause1303 q h, clause1304 q h, clause1305 q h, clause1306 q h, clause1307 q h, clause1308 q h, clause1309 q h, clause1310 q h, clause1311 q h, clause1312 q h⟩

end
end Snake9.Regrowth.E112024
