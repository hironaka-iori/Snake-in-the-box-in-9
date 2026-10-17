import E112020Semantics
import B112E020Inputs
namespace Snake9.Regrowth.E112020
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1667 = true := by
  have hs : count1667 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1667)) (countLit q [-75]) (countLit q [-76]) (count1667 q) 1 (meaningNeg75 q) (meaning1667 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1667 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1667 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1668 = true := by
  have hs : count1667 q = (countLit q [-75]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1668)) (countLit q [-75]) (countLit q [-76]) (count1667 q) 1 1 (meaningNeg75 q) (meaningNeg76 q) (meaning1668 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1668 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 76 = true ∨ valuation q 1668 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1669 = true := by
  have hs : count1669 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1669)) (countLit q [-78]) (countLit q [-80]) (count1669 q) 1 (meaningNeg80 q) (meaning1669 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1669 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1669 = true := by
  have hs : count1669 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1669)) (countLit q [-78]) (countLit q [-80]) (count1669 q) 1 (meaningNeg78 q) (meaning1669 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1669 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1669 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1670 = true := by
  have hs : count1669 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1670)) (countLit q [-78]) (countLit q [-80]) (count1669 q) 1 1 (meaningNeg78 q) (meaningNeg80 q) (meaning1670 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1670 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 80 = true ∨ valuation q 1670 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1669 = false ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-75, -76]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1669)) (literal (valuationOf q) (1671)) (countLit q [-75, -76]) (countLit q [-78, -80]) (count1671 q) 1 (meaning1669 q) (meaning1671 q) hs
  change valuationOf q 1669 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1669 = false ∨ valuation q 1671 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1670 = false ∨ valuationOf q 1672 = true := by
  have hs : count1671 q = (countLit q [-75, -76]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-78, -80])
  have hm := merge_right (literal (valuationOf q) (1670)) (literal (valuationOf q) (1672)) (countLit q [-75, -76]) (countLit q [-78, -80]) (count1671 q) 2 (meaning1670 q) (meaning1672 q) hs
  change valuationOf q 1670 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1670 = false ∨ valuation q 1672 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1671 = true := by
  have hs : count1671 q = (countLit q [-75, -76]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-78, -80])
  have hm := merge_left (literal (valuationOf q) (1667)) (literal (valuationOf q) (1671)) (countLit q [-75, -76]) (countLit q [-78, -80]) (count1671 q) 1 (meaning1667 q) (meaning1671 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1671 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1671 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1672 = true := by
  have hs : count1671 q = (countLit q [-75, -76]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1672)) (countLit q [-75, -76]) (countLit q [-78, -80]) (count1671 q) 1 1 (meaning1667 q) (meaning1669 q) (meaning1672 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1669 = false ∨ valuation q 1672 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1667 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1673 = true := by
  have hs : count1671 q = (countLit q [-75, -76]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1667)) (literal (valuationOf q) (1670)) (literal (valuationOf q) (1673)) (countLit q [-75, -76]) (countLit q [-78, -80]) (count1671 q) 1 2 (meaning1667 q) (meaning1670 q) (meaning1673 q) hs
  change valuationOf q 1667 = false ∨ valuationOf q 1670 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1667 = false ∨ valuation q 1670 = false ∨ valuation q 1673 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1672 = true := by
  have hs : count1671 q = (countLit q [-75, -76]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-78, -80])
  have hm := merge_left (literal (valuationOf q) (1668)) (literal (valuationOf q) (1672)) (countLit q [-75, -76]) (countLit q [-78, -80]) (count1671 q) 2 (meaning1668 q) (meaning1672 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1672 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1672 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1668 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1673 = true := by
  have hs : count1671 q = (countLit q [-75, -76]) + (countLit q [-78, -80]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-78, -80])
  have hm := merge_two (literal (valuationOf q) (1668)) (literal (valuationOf q) (1669)) (literal (valuationOf q) (1673)) (countLit q [-75, -76]) (countLit q [-78, -80]) (count1671 q) 2 1 (meaning1668 q) (meaning1669 q) (meaning1673 q) hs
  change valuationOf q 1668 = false ∨ valuationOf q 1669 = false ∨ valuationOf q 1673 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1668 = false ∨ valuation q 1669 = false ∨ valuation q 1673 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1675 = true := by
  have hs : count1675 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1675)) (countLit q [-83]) (countLit q [-84]) (count1675 q) 1 (meaningNeg84 q) (meaning1675 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1675 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1675 = true := by
  have hs : count1675 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1675)) (countLit q [-83]) (countLit q [-84]) (count1675 q) 1 (meaningNeg83 q) (meaning1675 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1675 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1675 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 84 = true ∨ valuationOf q 1676 = true := by
  have hs : count1675 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-84)) (literal (valuationOf q) (1676)) (countLit q [-83]) (countLit q [-84]) (count1675 q) 1 1 (meaningNeg83 q) (meaningNeg84 q) (meaning1676 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 84)) = false ∨ valuationOf q 1676 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 84 = true ∨ valuation q 1676 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1677 = true := by
  have hs : count1677 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1677)) (countLit q [-88]) (countLit q [-91]) (count1677 q) 1 (meaningNeg91 q) (meaning1677 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1677 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1677 = true := by
  have hs : count1677 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1677)) (countLit q [-88]) (countLit q [-91]) (count1677 q) 1 (meaningNeg88 q) (meaning1677 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1677 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1677 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1678 = true := by
  have hs : count1677 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1678)) (countLit q [-88]) (countLit q [-91]) (count1677 q) 1 1 (meaningNeg88 q) (meaningNeg91 q) (meaning1678 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1678 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 1678 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1677 = false ∨ valuationOf q 1679 = true := by
  have hs : count1679 q = (countLit q [-83, -84]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-88, -91])
  have hm := merge_right (literal (valuationOf q) (1677)) (literal (valuationOf q) (1679)) (countLit q [-83, -84]) (countLit q [-88, -91]) (count1679 q) 1 (meaning1677 q) (meaning1679 q) hs
  change valuationOf q 1677 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1677 = false ∨ valuation q 1679 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1678 = false ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-83, -84]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-88, -91])
  have hm := merge_right (literal (valuationOf q) (1678)) (literal (valuationOf q) (1680)) (countLit q [-83, -84]) (countLit q [-88, -91]) (count1679 q) 2 (meaning1678 q) (meaning1680 q) hs
  change valuationOf q 1678 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1678 = false ∨ valuation q 1680 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1679 = true := by
  have hs : count1679 q = (countLit q [-83, -84]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-88, -91])
  have hm := merge_left (literal (valuationOf q) (1675)) (literal (valuationOf q) (1679)) (countLit q [-83, -84]) (countLit q [-88, -91]) (count1679 q) 1 (meaning1675 q) (meaning1679 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1679 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1679 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-83, -84]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-88, -91])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1680)) (countLit q [-83, -84]) (countLit q [-88, -91]) (count1679 q) 1 1 (meaning1675 q) (meaning1677 q) (meaning1680 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1677 = false ∨ valuation q 1680 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1675 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1681 = true := by
  have hs : count1679 q = (countLit q [-83, -84]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-88, -91])
  have hm := merge_two (literal (valuationOf q) (1675)) (literal (valuationOf q) (1678)) (literal (valuationOf q) (1681)) (countLit q [-83, -84]) (countLit q [-88, -91]) (count1679 q) 1 2 (meaning1675 q) (meaning1678 q) (meaning1681 q) hs
  change valuationOf q 1675 = false ∨ valuationOf q 1678 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1675 = false ∨ valuation q 1678 = false ∨ valuation q 1681 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1680 = true := by
  have hs : count1679 q = (countLit q [-83, -84]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-88, -91])
  have hm := merge_left (literal (valuationOf q) (1676)) (literal (valuationOf q) (1680)) (countLit q [-83, -84]) (countLit q [-88, -91]) (count1679 q) 2 (meaning1676 q) (meaning1680 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1680 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1680 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1676 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1681 = true := by
  have hs : count1679 q = (countLit q [-83, -84]) + (countLit q [-88, -91]) := List.countP_append (p := literal q) (l₁ := [-83, -84]) (l₂ := [-88, -91])
  have hm := merge_two (literal (valuationOf q) (1676)) (literal (valuationOf q) (1677)) (literal (valuationOf q) (1681)) (countLit q [-83, -84]) (countLit q [-88, -91]) (count1679 q) 2 1 (meaning1676 q) (meaning1677 q) (meaning1681 q) hs
  change valuationOf q 1676 = false ∨ valuationOf q 1677 = false ∨ valuationOf q 1681 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1676 = false ∨ valuation q 1677 = false ∨ valuation q 1681 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1679 = false ∨ valuationOf q 1683 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_right (literal (valuationOf q) (1679)) (literal (valuationOf q) (1683)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 1 (meaning1679 q) (meaning1683 q) hs
  change valuationOf q 1679 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1679 = false ∨ valuation q 1683 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 1680 = false ∨ valuationOf q 1684 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_right (literal (valuationOf q) (1680)) (literal (valuationOf q) (1684)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 2 (meaning1680 q) (meaning1684 q) hs
  change valuationOf q 1680 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 1680 = false ∨ valuation q 1684 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 1681 = false ∨ valuationOf q 1685 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_right (literal (valuationOf q) (1681)) (literal (valuationOf q) (1685)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 3 (meaning1681 q) (meaning1685 q) hs
  change valuationOf q 1681 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 1681 = false ∨ valuation q 1685 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1683 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_left (literal (valuationOf q) (1671)) (literal (valuationOf q) (1683)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 1 (meaning1671 q) (meaning1683 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1683 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1683 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1684 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1679)) (literal (valuationOf q) (1684)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 1 1 (meaning1671 q) (meaning1679 q) (meaning1684 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1679 = false ∨ valuationOf q 1684 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1679 = false ∨ valuation q 1684 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1685 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1680)) (literal (valuationOf q) (1685)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 1 2 (meaning1671 q) (meaning1680 q) (meaning1685 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1680 = false ∨ valuationOf q 1685 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1680 = false ∨ valuation q 1685 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 1671 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1686 = true := by
  have hs : count1683 q = (countLit q [-75, -76, -78, -80]) + (countLit q [-83, -84, -88, -91]) := List.countP_append (p := literal q) (l₁ := [-75, -76, -78, -80]) (l₂ := [-83, -84, -88, -91])
  have hm := merge_two (literal (valuationOf q) (1671)) (literal (valuationOf q) (1681)) (literal (valuationOf q) (1686)) (countLit q [-75, -76, -78, -80]) (countLit q [-83, -84, -88, -91]) (count1683 q) 1 3 (meaning1671 q) (meaning1681 q) (meaning1686 q) hs
  change valuationOf q 1671 = false ∨ valuationOf q 1681 = false ∨ valuationOf q 1686 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 1671 = false ∨ valuation q 1681 = false ∨ valuation q 1686 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E020.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112020
