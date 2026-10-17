import E112008Semantics
import B112E008Inputs
namespace Snake9.Regrowth.E112008
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1666 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1659)) (literal (valuationOf q) (1666)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 3 1 (meaning1654 q) (meaning1659 q) (meaning1666 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1659 = false ∨ valuationOf q 1666 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1659 = false ∨ valuation q 1666 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1667 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1660)) (literal (valuationOf q) (1667)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 3 2 (meaning1654 q) (meaning1660 q) (meaning1667 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1660 = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1660 = false ∨ valuation q 1667 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 1654 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1668 = true := by
  have hs : count1663 q = (countLit q [-60, -62, -63]) + (countLit q [-65, -66, -68, -71]) := List.countP_append (p := literal q) (l₁ := [-60, -62, -63]) (l₂ := [-65, -66, -68, -71])
  have hm := merge_two (literal (valuationOf q) (1654)) (literal (valuationOf q) (1661)) (literal (valuationOf q) (1668)) (countLit q [-60, -62, -63]) (countLit q [-65, -66, -68, -71]) (count1663 q) 3 3 (meaning1654 q) (meaning1661 q) (meaning1668 q) hs
  change valuationOf q 1654 = false ∨ valuationOf q 1661 = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 1654 = false ∨ valuation q 1661 = false ∨ valuation q 1668 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (1670)) (countLit q [-73]) (countLit q [-74]) (count1670 q) 1 (meaningNeg74 q) (meaning1670 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1670 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1670 = true := by
  have hs : count1670 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1670)) (countLit q [-73]) (countLit q [-74]) (count1670 q) 1 (meaningNeg73 q) (meaning1670 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1670 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 74 = true ∨ valuationOf q 1671 = true := by
  have hs : count1670 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (1671)) (countLit q [-73]) (countLit q [-74]) (count1670 q) 1 1 (meaningNeg73 q) (meaningNeg74 q) (meaning1671 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 74 = true ∨ valuation q 1671 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-77]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1672)) (countLit q [-77]) (countLit q [-80]) (count1672 q) 1 (meaningNeg80 q) (meaning1672 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1672 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1672 = true := by
  have hs : count1672 q = (countLit q [-77]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1672)) (countLit q [-77]) (countLit q [-80]) (count1672 q) 1 (meaningNeg77 q) (meaning1672 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1672 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1672 = false ∨ valuationOf q 1674 = true := by
  have hs : count1674 q = (countLit q [-73, -74]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-77, -80])
  have hm := merge_right (literal (valuationOf q) (1672)) (literal (valuationOf q) (1674)) (countLit q [-73, -74]) (countLit q [-77, -80]) (count1674 q) 1 (meaning1672 q) (meaning1674 q) hs
  change valuationOf q 1672 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1672 = false ∨ valuation q 1674 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1674 = true := by
  have hs : count1674 q = (countLit q [-73, -74]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-77, -80])
  have hm := merge_left (literal (valuationOf q) (1670)) (literal (valuationOf q) (1674)) (countLit q [-73, -74]) (countLit q [-77, -80]) (count1674 q) 1 (meaning1670 q) (meaning1674 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1674 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1674 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1675 = true := by
  have hs : count1674 q = (countLit q [-73, -74]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-77, -80])
  have hm := merge_two (literal (valuationOf q) (1670)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1675)) (countLit q [-73, -74]) (countLit q [-77, -80]) (count1674 q) 1 1 (meaning1670 q) (meaning1672 q) (meaning1675 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1672 = false ∨ valuation q 1675 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1675 = true := by
  have hs : count1674 q = (countLit q [-73, -74]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-77, -80])
  have hm := merge_left (literal (valuationOf q) (1671)) (literal (valuationOf q) (1675)) (countLit q [-73, -74]) (countLit q [-77, -80]) (count1674 q) 2 (meaning1671 q) (meaning1675 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1675 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1676 = true := by
  have hs : count1674 q = (countLit q [-73, -74]) + (countLit q [-77, -80]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-77, -80])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1672)) (literal (valuationOf q) (1676)) (countLit q [-73, -74]) (countLit q [-77, -80]) (count1674 q) 2 1 (meaning1671 q) (meaning1672 q) (meaning1676 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1672 = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1672 = false ∨ valuation q 1676 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1678 = true := by
  have hs : count1678 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1678)) (countLit q [-82]) (countLit q [-83]) (count1678 q) 1 (meaningNeg83 q) (meaning1678 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1678 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1678 = true := by
  have hs : count1678 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1678)) (countLit q [-82]) (countLit q [-83]) (count1678 q) 1 (meaningNeg82 q) (meaning1678 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1678 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 83 = true ∨ valuationOf q 1679 = true := by
  have hs : count1678 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-83)) (literal (valuationOf q) (1679)) (countLit q [-82]) (countLit q [-83]) (count1678 q) 1 1 (meaningNeg82 q) (meaningNeg83 q) (meaning1679 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 83)) = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 83 = true ∨ valuation q 1679 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1680 = true := by
  have hs : count1680 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1680)) (countLit q [-86]) (countLit q [-89]) (count1680 q) 1 (meaningNeg89 q) (meaning1680 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1680 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1680 = true := by
  have hs : count1680 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1680)) (countLit q [-86]) (countLit q [-89]) (count1680 q) 1 (meaningNeg86 q) (meaning1680 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1680 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1681 = true := by
  have hs : count1680 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1681)) (countLit q [-86]) (countLit q [-89]) (count1680 q) 1 1 (meaningNeg86 q) (meaningNeg89 q) (meaning1681 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 1681 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1682 = true := by
  have hs : count1682 q = (countLit q [-82, -83]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1680)) (literal (valuationOf q) (1682)) (countLit q [-82, -83]) (countLit q [-86, -89]) (count1682 q) 1 (meaning1680 q) (meaning1682 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1682 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1683 = true := by
  have hs : count1682 q = (countLit q [-82, -83]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1681)) (literal (valuationOf q) (1683)) (countLit q [-82, -83]) (countLit q [-86, -89]) (count1682 q) 2 (meaning1681 q) (meaning1683 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1683 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1682 = true := by
  have hs : count1682 q = (countLit q [-82, -83]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -89])
  have hm := merge_left (literal (valuationOf q) (1678)) (literal (valuationOf q) (1682)) (countLit q [-82, -83]) (countLit q [-86, -89]) (count1682 q) 1 (meaning1678 q) (meaning1682 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1682 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1682 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1683 = true := by
  have hs : count1682 q = (countLit q [-82, -83]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1683)) (countLit q [-82, -83]) (countLit q [-86, -89]) (count1682 q) 1 1 (meaning1678 q) (meaning1680 q) (meaning1683 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1680 = false ∨ valuation q 1683 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1684 = true := by
  have hs : count1682 q = (countLit q [-82, -83]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1678)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1684)) (countLit q [-82, -83]) (countLit q [-86, -89]) (count1682 q) 1 2 (meaning1678 q) (meaning1681 q) (meaning1684 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1681 = false ∨ valuation q 1684 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1683 = true := by
  have hs : count1682 q = (countLit q [-82, -83]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -89])
  have hm := merge_left (literal (valuationOf q) (1679)) (literal (valuationOf q) (1683)) (countLit q [-82, -83]) (countLit q [-86, -89]) (count1682 q) 2 (meaning1679 q) (meaning1683 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1683 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1684 = true := by
  have hs : count1682 q = (countLit q [-82, -83]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1684)) (countLit q [-82, -83]) (countLit q [-86, -89]) (count1682 q) 2 1 (meaning1679 q) (meaning1680 q) (meaning1684 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1680 = false ∨ valuation q 1684 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1685 = true := by
  have hs : count1682 q = (countLit q [-82, -83]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1679)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1685)) (countLit q [-82, -83]) (countLit q [-86, -89]) (count1682 q) 2 2 (meaning1679 q) (meaning1681 q) (meaning1685 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1681 = false ∨ valuation q 1685 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1682 = false ∨ valuationOf q 1686 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1682)) (literal (valuationOf q) (1686)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 1 (meaning1682 q) (meaning1686 q) hs
  change valuationOf q 1682 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1682 = false ∨ valuation q 1686 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1683 = false ∨ valuationOf q 1687 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1683)) (literal (valuationOf q) (1687)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 2 (meaning1683 q) (meaning1687 q) hs
  change valuationOf q 1683 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1683 = false ∨ valuation q 1687 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1684 = false ∨ valuationOf q 1688 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1684)) (literal (valuationOf q) (1688)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 3 (meaning1684 q) (meaning1688 q) hs
  change valuationOf q 1684 = false ∨ valuationOf q 1688 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1684 = false ∨ valuation q 1688 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1686 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1674)) (literal (valuationOf q) (1686)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 1 (meaning1674 q) (meaning1686 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1686 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1674 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true := by
  have hs : count1686 q = (countLit q [-73, -74, -77, -80]) + (countLit q [-82, -83, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-73, -74, -77, -80]) (l₂ := [-82, -83, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1674)) (literal (valuationOf q) (1682)) (literal (valuationOf q) (1687)) (countLit q [-73, -74, -77, -80]) (countLit q [-82, -83, -86, -89]) (count1686 q) 1 1 (meaning1674 q) (meaning1682 q) (meaning1687 q) hs
  change valuationOf q 1674 = false ∨ valuationOf q 1682 = false ∨ valuationOf q 1687 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1674 = false ∨ valuation q 1682 = false ∨ valuation q 1687 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E008.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112008
