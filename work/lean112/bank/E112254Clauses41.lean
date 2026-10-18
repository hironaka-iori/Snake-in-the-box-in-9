import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1734)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 3 2 (meaning1701 q) (meaning1723 q) (meaning1734 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1723 = false ∨ valuation q 1734 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1735 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1735)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 3 3 (meaning1701 q) (meaning1724 q) (meaning1735 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1724 = false ∨ valuation q 1735 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1736 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1736)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 3 4 (meaning1701 q) (meaning1725 q) (meaning1736 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1725 = false ∨ valuation q 1736 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1701 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1737 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1701)) (literal (valuationOf q) (1726)) (literal (valuationOf q) (1737)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 3 5 (meaning1701 q) (meaning1726 q) (meaning1737 q) hs
  change valuationOf q 1701 = false ∨ valuationOf q 1726 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1701 = false ∨ valuation q 1726 = false ∨ valuation q 1737 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1733 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_left (literal (valuationOf q) (1702)) (literal (valuationOf q) (1733)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 4 (meaning1702 q) (meaning1733 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1733 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1734)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 4 1 (meaning1702 q) (meaning1722 q) (meaning1734 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1722 = false ∨ valuation q 1734 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1735 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1735)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 4 2 (meaning1702 q) (meaning1723 q) (meaning1735 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1723 = false ∨ valuation q 1735 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1736 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1736)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 4 3 (meaning1702 q) (meaning1724 q) (meaning1736 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1724 = false ∨ valuation q 1736 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1702 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1737 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1702)) (literal (valuationOf q) (1725)) (literal (valuationOf q) (1737)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 4 4 (meaning1702 q) (meaning1725 q) (meaning1737 q) hs
  change valuationOf q 1702 = false ∨ valuationOf q 1725 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1702 = false ∨ valuation q 1725 = false ∨ valuation q 1737 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1734 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_left (literal (valuationOf q) (1703)) (literal (valuationOf q) (1734)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 5 (meaning1703 q) (meaning1734 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1734 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1735 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1722)) (literal (valuationOf q) (1735)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 5 1 (meaning1703 q) (meaning1722 q) (meaning1735 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1722 = false ∨ valuationOf q 1735 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1722 = false ∨ valuation q 1735 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1736 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1736)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 5 2 (meaning1703 q) (meaning1723 q) (meaning1736 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1736 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1723 = false ∨ valuation q 1736 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1703 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1737 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1703)) (literal (valuationOf q) (1724)) (literal (valuationOf q) (1737)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 5 3 (meaning1703 q) (meaning1724 q) (meaning1737 q) hs
  change valuationOf q 1703 = false ∨ valuationOf q 1724 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1703 = false ∨ valuation q 1724 = false ∨ valuation q 1737 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1704 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1737 = true := by
  have hs : count1730 q = (countLit q [-94, -97, -99, -100, -101, -102, -103]) + (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-94, -97, -99, -100, -101, -102, -103]) (l₂ := [-105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1704)) (literal (valuationOf q) (1723)) (literal (valuationOf q) (1737)) (countLit q [-94, -97, -99, -100, -101, -102, -103]) (countLit q [-105, -108, -110, -111, -114, -117, -121, -122]) (count1730 q) 6 2 (meaning1704 q) (meaning1723 q) (meaning1737 q) hs
  change valuationOf q 1704 = false ∨ valuationOf q 1723 = false ∨ valuationOf q 1737 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1704 = false ∨ valuation q 1723 = false ∨ valuation q 1737 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 1 7 (meaning1672 q) (meaning1736 q) (meaning1752 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1736 = false ∨ valuation q 1752 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1672)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 1 8 (meaning1672 q) (meaning1737 q) (meaning1753 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1737 = false ∨ valuation q 1753 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 2 6 (meaning1673 q) (meaning1735 q) (meaning1752 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1735 = false ∨ valuation q 1752 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 2 7 (meaning1673 q) (meaning1736 q) (meaning1753 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1736 = false ∨ valuation q 1753 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1673 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1673)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 2 8 (meaning1673 q) (meaning1737 q) (meaning1754 q) hs
  change valuationOf q 1673 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1673 = false ∨ valuation q 1737 = false ∨ valuation q 1754 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 3 5 (meaning1674 q) (meaning1734 q) (meaning1752 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1734 = false ∨ valuation q 1752 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 3 6 (meaning1674 q) (meaning1735 q) (meaning1753 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1735 = false ∨ valuation q 1753 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 3 7 (meaning1674 q) (meaning1736 q) (meaning1754 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1736 = false ∨ valuation q 1754 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 4 4 (meaning1675 q) (meaning1733 q) (meaning1752 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1733 = false ∨ valuation q 1752 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 4 5 (meaning1675 q) (meaning1734 q) (meaning1753 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1734 = false ∨ valuation q 1753 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 4 6 (meaning1675 q) (meaning1735 q) (meaning1754 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1735 = false ∨ valuation q 1754 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 4 7 (meaning1675 q) (meaning1736 q) (meaning1755 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1736 = false ∨ valuation q 1755 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1752 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1732)) (literal (valuationOf q) (1752)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 5 3 (meaning1676 q) (meaning1732 q) (meaning1752 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1732 = false ∨ valuationOf q 1752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1732 = false ∨ valuation q 1752 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1753 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1733)) (literal (valuationOf q) (1753)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 5 4 (meaning1676 q) (meaning1733 q) (meaning1753 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1733 = false ∨ valuationOf q 1753 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1733 = false ∨ valuation q 1753 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1754 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1734)) (literal (valuationOf q) (1754)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 5 5 (meaning1676 q) (meaning1734 q) (meaning1754 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1734 = false ∨ valuationOf q 1754 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1734 = false ∨ valuation q 1754 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1755 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1735)) (literal (valuationOf q) (1755)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 5 6 (meaning1676 q) (meaning1735 q) (meaning1755 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1735 = false ∨ valuationOf q 1755 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1735 = false ∨ valuation q 1755 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1756 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1736)) (literal (valuationOf q) (1756)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 5 7 (meaning1676 q) (meaning1736 q) (meaning1756 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1736 = false ∨ valuationOf q 1756 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1736 = false ∨ valuation q 1756 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1757 = true := by
  have hs : count1745 q = (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) + (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (l₂ := [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1737)) (literal (valuationOf q) (1757)) (countLit q [-65, -66, -67, -69, -70, -77, -78, -79, -81, -82, -83, -86, -87, -92]) (countLit q [-94, -97, -99, -100, -101, -102, -103, -105, -108, -110, -111, -114, -117, -121, -122]) (count1745 q) 5 8 (meaning1676 q) (meaning1737 q) (meaning1757 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1737 = false ∨ valuationOf q 1757 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1737 = false ∨ valuation q 1757 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E254.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112254
