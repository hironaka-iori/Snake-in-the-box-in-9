import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 115 = true ∨ valuationOf q 117 = true ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-115]) + (countLit q [-117]) := List.countP_append (p := literal q) (l₁ := [-115]) (l₂ := [-117])
  have hm := merge_two (literal (valuationOf q) (-115)) (literal (valuationOf q) (-117)) (literal (valuationOf q) (1647)) (countLit q [-115]) (countLit q [-117]) (count1646 q) 1 1 (meaningNeg115 q) (meaningNeg117 q) (meaning1647 q) hs
  change (! (valuationOf q 115)) = false ∨ (! (valuationOf q 117)) = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 115 = true ∨ valuation q 117 = true ∨ valuation q 1647 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1648 = true := by
  have hs : count1648 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1646)) (literal (valuationOf q) (1648)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1648 q) 1 (meaning1646 q) (meaning1648 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1648 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1649 = true := by
  have hs : count1648 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_right (literal (valuationOf q) (1647)) (literal (valuationOf q) (1649)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1648 q) 2 (meaning1647 q) (meaning1649 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1649 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1648 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1648 q) 1 (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1648 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1649 = true := by
  have hs : count1648 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_two (literal (valuationOf q) (1644)) (literal (valuationOf q) (1646)) (literal (valuationOf q) (1649)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1648 q) 1 1 (meaning1644 q) (meaning1646 q) (meaning1649 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1646 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1646 = false ∨ valuation q 1649 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1649 = true := by
  have hs : count1648 q = (countLit q [-111, -114]) + (countLit q [-115, -117]) := List.countP_append (p := literal q) (l₁ := [-111, -114]) (l₂ := [-115, -117])
  have hm := merge_left (literal (valuationOf q) (1645)) (literal (valuationOf q) (1649)) (countLit q [-111, -114]) (countLit q [-115, -117]) (count1648 q) 2 (meaning1645 q) (meaning1649 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1649 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1648 = false ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1648)) (literal (valuationOf q) (1652)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 1 (meaning1648 q) (meaning1652 q) hs
  change valuationOf q 1648 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1648 = false ∨ valuation q 1652 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1649 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1649)) (literal (valuationOf q) (1653)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 2 (meaning1649 q) (meaning1653 q) hs
  change valuationOf q 1649 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1649 = false ∨ valuation q 1653 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1652 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1640)) (literal (valuationOf q) (1652)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 1 (meaning1640 q) (meaning1652 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1652 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1653)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 1 1 (meaning1640 q) (meaning1648 q) (meaning1653 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1648 = false ∨ valuation q 1653 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1654 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1640)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1654)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 1 2 (meaning1640 q) (meaning1649 q) (meaning1654 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1649 = false ∨ valuation q 1654 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1653 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1641)) (literal (valuationOf q) (1653)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 2 (meaning1641 q) (meaning1653 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1653 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1653 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1654 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1654)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 2 1 (meaning1641 q) (meaning1648 q) (meaning1654 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1648 = false ∨ valuation q 1654 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1655 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1641)) (literal (valuationOf q) (1649)) (literal (valuationOf q) (1655)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 2 2 (meaning1641 q) (meaning1649 q) (meaning1655 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1649 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1649 = false ∨ valuation q 1655 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1654 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1642)) (literal (valuationOf q) (1654)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 3 (meaning1642 q) (meaning1654 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1654 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1654 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1655 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1648)) (literal (valuationOf q) (1655)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 3 1 (meaning1642 q) (meaning1648 q) (meaning1655 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1648 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1648 = false ∨ valuation q 1655 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1655 = true := by
  have hs : count1652 q = (countLit q [-104, -105, -106, -108]) + (countLit q [-111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-104, -105, -106, -108]) (l₂ := [-111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1643)) (literal (valuationOf q) (1655)) (countLit q [-104, -105, -106, -108]) (countLit q [-111, -114, -115, -117]) (count1652 q) 4 (meaning1643 q) (meaning1655 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1655 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1655 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1652 = false ∨ valuationOf q 1660 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1652)) (literal (valuationOf q) (1660)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 1 (meaning1652 q) (meaning1660 q) hs
  change valuationOf q 1652 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1652 = false ∨ valuation q 1660 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1653 = false ∨ valuationOf q 1661 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_right (literal (valuationOf q) (1653)) (literal (valuationOf q) (1661)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 2 (meaning1653 q) (meaning1661 q) hs
  change valuationOf q 1653 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1653 = false ∨ valuation q 1661 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1660 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1629)) (literal (valuationOf q) (1660)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 1 (meaning1629 q) (meaning1660 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1660 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1660 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1661 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1661)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 1 1 (meaning1629 q) (meaning1652 q) (meaning1661 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1652 = false ∨ valuation q 1661 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1662 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1662)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 1 2 (meaning1629 q) (meaning1653 q) (meaning1662 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1653 = false ∨ valuation q 1662 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1663 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1663)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 1 3 (meaning1629 q) (meaning1654 q) (meaning1663 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1654 = false ∨ valuation q 1663 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1661 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1630)) (literal (valuationOf q) (1661)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 2 (meaning1630 q) (meaning1661 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1661 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1661 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1662)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 2 1 (meaning1630 q) (meaning1652 q) (meaning1662 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1652 = false ∨ valuation q 1662 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1663 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1663)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 2 2 (meaning1630 q) (meaning1653 q) (meaning1663 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1653 = false ∨ valuation q 1663 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1664 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1664)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 2 3 (meaning1630 q) (meaning1654 q) (meaning1664 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1654 = false ∨ valuation q 1664 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1630 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1665 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1630)) (literal (valuationOf q) (1655)) (literal (valuationOf q) (1665)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 2 4 (meaning1630 q) (meaning1655 q) (meaning1665 q) hs
  change valuationOf q 1630 = false ∨ valuationOf q 1655 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1630 = false ∨ valuation q 1655 = false ∨ valuation q 1665 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1662 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_left (literal (valuationOf q) (1631)) (literal (valuationOf q) (1662)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 3 (meaning1631 q) (meaning1662 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1662 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1662 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1663 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1652)) (literal (valuationOf q) (1663)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 3 1 (meaning1631 q) (meaning1652 q) (meaning1663 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1652 = false ∨ valuationOf q 1663 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1652 = false ∨ valuation q 1663 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1664 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1653)) (literal (valuationOf q) (1664)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 3 2 (meaning1631 q) (meaning1653 q) (meaning1664 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1653 = false ∨ valuationOf q 1664 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1653 = false ∨ valuation q 1664 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1631 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1665 = true := by
  have hs : count1660 q = (countLit q [-90, -92, -95, -96, -97, -98, -102]) + (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) := List.countP_append (p := literal q) (l₁ := [-90, -92, -95, -96, -97, -98, -102]) (l₂ := [-104, -105, -106, -108, -111, -114, -115, -117])
  have hm := merge_two (literal (valuationOf q) (1631)) (literal (valuationOf q) (1654)) (literal (valuationOf q) (1665)) (countLit q [-90, -92, -95, -96, -97, -98, -102]) (countLit q [-104, -105, -106, -108, -111, -114, -115, -117]) (count1660 q) 3 3 (meaning1631 q) (meaning1654 q) (meaning1665 q) hs
  change valuationOf q 1631 = false ∨ valuationOf q 1654 = false ∨ valuationOf q 1665 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1631 = false ∨ valuation q 1654 = false ∨ valuation q 1665 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E027.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112027
