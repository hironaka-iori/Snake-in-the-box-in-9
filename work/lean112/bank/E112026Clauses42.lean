import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1729 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1704)) (literal (valuationOf q) (1729)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 9 4 (meaning1645 q) (meaning1704 q) (meaning1729 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1704 = false ∨ valuationOf q 1729 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1704 = false ∨ valuation q 1729 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1730 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1705)) (literal (valuationOf q) (1730)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 9 5 (meaning1645 q) (meaning1705 q) (meaning1730 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1705 = false ∨ valuationOf q 1730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1705 = false ∨ valuation q 1730 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1731 = true := by
  have hs : count1717 q = (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) + (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (l₂ := [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1645)) (literal (valuationOf q) (1706)) (literal (valuationOf q) (1731)) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89]) (countLit q [-91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1717 q) 9 6 (meaning1645 q) (meaning1706 q) (meaning1731 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1706 = false ∨ valuationOf q 1731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1706 = false ∨ valuation q 1731 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) + (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (l₂ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 8 15 (meaning1573 q) (meaning1731 q) (meaning1762 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1731 = false ∨ valuation q 1762 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) + (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (l₂ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1730)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 9 14 (meaning1574 q) (meaning1730 q) (meaning1762 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1730 = false ∨ valuation q 1762 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) + (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (l₂ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1729)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 10 13 (meaning1575 q) (meaning1729 q) (meaning1762 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1729 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1729 = false ∨ valuation q 1762 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) + (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (l₂ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1576)) (literal (valuationOf q) (1728)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 11 12 (meaning1576 q) (meaning1728 q) (meaning1762 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1728 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1728 = false ∨ valuation q 1762 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) + (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (l₂ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1577)) (literal (valuationOf q) (1727)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 12 11 (meaning1577 q) (meaning1727 q) (meaning1762 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1727 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1727 = false ∨ valuation q 1762 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) + (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (l₂ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 13 10 (meaning1578 q) (meaning1726 q) (meaning1762 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1726 = false ∨ valuation q 1762 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) + (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (l₂ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 14 9 (meaning1579 q) (meaning1725 q) (meaning1762 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1725 = false ∨ valuation q 1762 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1762 = true := by
  have hs : count1740 q = (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) + (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (l₂ := [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1762)) (countLit q [-1, -3, -5, -6, -8, -10, -11, -13, -14, -18, -19, -20, -22, -25, -26, -28, -31, -33, -35, -36, -37, -39, -41, -43, -44, -47, -50, -52, -53, -54, -55]) (countLit q [-57, -60, -62, -63, -67, -69, -70, -72, -74, -76, -77, -79, -81, -85, -86, -89, -91, -93, -94, -96, -98, -99, -102, -105, -107, -108, -110, -111, -115, -117, -118, -119]) (count1740 q) 15 8 (meaning1580 q) (meaning1724 q) (meaning1762 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1762 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1724 = false ∨ valuation q 1762 = true := counterClause1355 (baseVal q)

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1762 = false := by
  rw [value1762]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1740 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 4 = false ∨ valuation q 9 = false ∨ valuation q 11 = false := by
  rw [value1, value4, value9, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (35 : Vertex) (39 : Vertex) (99 : Vertex) (103 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 9 = false ∨ valuation q 15 = false ∨ valuation q 33 = false := by
  rw [value1, value9, value15, value33]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (35 : Vertex) (99 : Vertex) (163 : Vertex) (227 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 13 = false ∨ valuation q 22 = false ∨ valuation q 23 = false := by
  rw [value12, value13, value22, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (161 : Vertex) (176 : Vertex) (177 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 22 = false ∨ valuation q 27 = false := by
  rw [value12, value18, value22, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (176 : Vertex) (184 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 12 = false ∨ valuation q 18 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value12, value18, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (160 : Vertex) (168 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 14 = false ∨ valuation q 17 = false ∨ valuation q 24 = false ∨ valuation q 26 = false := by
  rw [value14, value17, value24, value26]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (162 : Vertex) (166 : Vertex) (178 : Vertex) (182 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 33 = false ∨ valuation q 38 = false := by
  rw [value15, value19, value33, value38]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (163 : Vertex) (171 : Vertex) (227 : Vertex) (235 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 17 = false ∨ valuation q 36 = false ∨ valuation q 86 = false ∨ valuation q 106 = false := by
  rw [value17, value36, value86, value106]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (166 : Vertex) (230 : Vertex) (422 : Vertex) (486 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 18 = false ∨ valuation q 27 = false ∨ valuation q 88 = false ∨ valuation q 99 = false := by
  rw [value18, value27, value88, value99]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (168 : Vertex) (184 : Vertex) (424 : Vertex) (440 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 20 = false ∨ valuation q 21 = false ∨ valuation q 29 = false ∨ valuation q 31 = false := by
  rw [value20, value21, value29, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (173 : Vertex) (175 : Vertex) (189 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 22 = false ∨ valuation q 23 = false ∨ valuation q 24 = false ∨ valuation q 25 = false := by
  rw [value22, value23, value24, value25]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (176 : Vertex) (177 : Vertex) (178 : Vertex) (179 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 23 = false ∨ valuation q 25 = false ∨ valuation q 94 = false ∨ valuation q 95 = false := by
  rw [value23, value25, value94, value95]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (177 : Vertex) (179 : Vertex) (433 : Vertex) (435 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 28 = false ∨ valuation q 29 = false ∨ valuation q 30 = false ∨ valuation q 31 = false := by
  rw [value28, value29, value30, value31]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (188 : Vertex) (189 : Vertex) (190 : Vertex) (191 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 32 = false ∨ valuation q 36 = false ∨ valuation q 37 = false ∨ valuation q 40 = false := by
  rw [value32, value36, value37, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (226 : Vertex) (230 : Vertex) (234 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 35 = false ∨ valuation q 41 = false ∨ valuation q 42 = false := by
  rw [value34, value35, value41, value42]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (229 : Vertex) (244 : Vertex) (245 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 34 = false ∨ valuation q 36 = false ∨ valuation q 39 = false ∨ valuation q 40 = false := by
  rw [value34, value36, value39, value40]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (228 : Vertex) (230 : Vertex) (236 : Vertex) (238 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 44 = false ∨ valuation q 45 = false ∨ valuation q 46 = false ∨ valuation q 47 = false := by
  rw [value44, value45, value46, value47]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (248 : Vertex) (249 : Vertex) (250 : Vertex) (251 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 50 = false ∨ valuation q 57 = false ∨ valuation q 58 = false := by
  rw [value49, value50, value57, value58]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (289 : Vertex) (304 : Vertex) (305 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 49 = false ∨ valuation q 53 = false ∨ valuation q 81 = false ∨ valuation q 88 = false := by
  rw [value49, value53, value81, value88]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (288 : Vertex) (296 : Vertex) (416 : Vertex) (424 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 54 = false ∨ valuation q 56 = false ∨ valuation q 90 = false ∨ valuation q 93 = false := by
  rw [value54, value56, value90, value93]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (299 : Vertex) (303 : Vertex) (427 : Vertex) (431 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E026.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112026
