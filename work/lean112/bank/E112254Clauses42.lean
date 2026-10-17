import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 6 2 (meaning1677 q) (meaning1731 q) (meaning1752 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1731 = false ∨ valuation q 1752 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 6 3 (meaning1677 q) (meaning1732 q) (meaning1753 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1732 = false ∨ valuation q 1753 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 6 4 (meaning1677 q) (meaning1733 q) (meaning1754 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1733 = false ∨ valuation q 1754 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 6 5 (meaning1677 q) (meaning1734 q) (meaning1755 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1734 = false ∨ valuation q 1755 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 6 6 (meaning1677 q) (meaning1735 q) (meaning1756 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1735 = false ∨ valuation q 1756 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1757 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1677)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1757)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 6 7 (meaning1677 q) (meaning1736 q) (meaning1757 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1736 = false ∨ valuation q 1757 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1730)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 7 1 (meaning1678 q) (meaning1730 q) (meaning1752 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1730 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1730 = false ∨ valuation q 1752 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 7 2 (meaning1678 q) (meaning1731 q) (meaning1753 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1731 = false ∨ valuation q 1753 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 7 3 (meaning1678 q) (meaning1732 q) (meaning1754 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1732 = false ∨ valuation q 1754 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 7 4 (meaning1678 q) (meaning1733 q) (meaning1755 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1733 = false ∨ valuation q 1755 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 7 5 (meaning1678 q) (meaning1734 q) (meaning1756 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1734 = false ∨ valuation q 1756 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1757 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1757)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 7 6 (meaning1678 q) (meaning1735 q) (meaning1757 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1735 = false ∨ valuation q 1757 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 8 2 (meaning1679 q) (meaning1731 q) (meaning1754 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1731 = false ∨ valuation q 1754 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 8 3 (meaning1679 q) (meaning1732 q) (meaning1755 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1732 = false ∨ valuation q 1755 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 8 4 (meaning1679 q) (meaning1733 q) (meaning1756 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1733 = false ∨ valuation q 1756 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1757 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1757)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 8 5 (meaning1679 q) (meaning1734 q) (meaning1757 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1734 = false ∨ valuation q 1757 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1758 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1758)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 8 6 (meaning1679 q) (meaning1735 q) (meaning1758 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1735 = false ∨ valuation q 1758 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 9 2 (meaning1680 q) (meaning1731 q) (meaning1755 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1731 = false ∨ valuation q 1755 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1680)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 9 3 (meaning1680 q) (meaning1732 q) (meaning1756 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1732 = false ∨ valuation q 1756 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1681)) (literal (valuationOf q) (1731)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 10 2 (meaning1681 q) (meaning1731 q) (meaning1756 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1731 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1731 = false ∨ valuation q 1756 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) + (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (l₂ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1617)) (literal (valuationOf q) (1758)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1763 q) 4 14 (meaning1617 q) (meaning1758 q) (meaning1780 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1758 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1758 = false ∨ valuation q 1780 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) + (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (l₂ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1618)) (literal (valuationOf q) (1757)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1763 q) 5 13 (meaning1618 q) (meaning1757 q) (meaning1780 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1757 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1757 = false ∨ valuation q 1780 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) + (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (l₂ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1619)) (literal (valuationOf q) (1756)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1763 q) 6 12 (meaning1619 q) (meaning1756 q) (meaning1780 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1756 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1756 = false ∨ valuation q 1780 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) + (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (l₂ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1620)) (literal (valuationOf q) (1755)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1763 q) 7 11 (meaning1620 q) (meaning1755 q) (meaning1780 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1755 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1755 = false ∨ valuation q 1780 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) + (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (l₂ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1621)) (literal (valuationOf q) (1754)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1763 q) 8 10 (meaning1621 q) (meaning1754 q) (meaning1780 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1754 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1754 = false ∨ valuation q 1780 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) + (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (l₂ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1753)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1763 q) 9 9 (meaning1622 q) (meaning1753 q) (meaning1780 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1753 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1753 = false ∨ valuation q 1780 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1780 = true := by
  have hs : count1763 q = (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) + (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (l₂ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1752)) (literal (valuationOf q) (1780)) (countLit q [-2, -5, -8, -9, -12, -14, -15, -18, -19, -22, -25, -27, -29, -31, -32, -34, -36, -38, -41, -44, -45, -47, -48, -51, -53, -55, -58, -59, -62]) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92, -94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1763 q) 10 8 (meaning1623 q) (meaning1752 q) (meaning1780 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1752 = false ∨ valuationOf q 1780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1752 = false ∨ valuation q 1780 = true := counterClause1371 (baseVal q)

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 1780 = false := by
  rw [value1780]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1763 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 65 = false ∨ valuation q 71 = false := by
  rw [value6, value12, value65, value71]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (257 : Vertex) (265 : Vertex) (385 : Vertex) (393 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 7 = false ∨ valuation q 9 = false ∨ valuation q 66 = false ∨ valuation q 68 = false := by
  rw [value7, value9, value66, value68]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (258 : Vertex) (262 : Vertex) (386 : Vertex) (390 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 10 = false ∨ valuation q 26 = false ∨ valuation q 27 = false := by
  rw [value8, value10, value26, value27]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (261 : Vertex) (263 : Vertex) (293 : Vertex) (295 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 15 = false ∨ valuation q 19 = false ∨ valuation q 23 = false := by
  rw [value10, value15, value19, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (263 : Vertex) (271 : Vertex) (279 : Vertex) (287 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E254.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112254
