import E112089Semantics
import B112E089Inputs
namespace Snake9.Regrowth.E112089
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_left (literal (valuationOf q) (-9)) (literal (valuationOf q) (1510)) (countLit q [-9]) (countLit q [-10]) (count1510 q) 1 (meaningNeg9 q) (meaning1510 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1510 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 10 = true ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-9]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-9]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-9)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (1511)) (countLit q [-9]) (countLit q [-10]) (count1510 q) 1 1 (meaningNeg9 q) (meaningNeg10 q) (meaning1511 q) hs
  change (! (valuationOf q 9)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 10 = true ∨ valuation q 1511 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_right (literal (valuationOf q) (-13)) (literal (valuationOf q) (1512)) (countLit q [-11]) (countLit q [-13]) (count1512 q) 1 (meaningNeg13 q) (meaning1512 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1512 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_left (literal (valuationOf q) (-11)) (literal (valuationOf q) (1512)) (countLit q [-11]) (countLit q [-13]) (count1512 q) 1 (meaningNeg11 q) (meaning1512 q) hs
  change (! (valuationOf q 11)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 1512 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 11 = true ∨ valuationOf q 13 = true ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-11]) + (countLit q [-13]) := List.countP_append (p := literal q) (l₁ := [-11]) (l₂ := [-13])
  have hm := merge_two (literal (valuationOf q) (-11)) (literal (valuationOf q) (-13)) (literal (valuationOf q) (1513)) (countLit q [-11]) (countLit q [-13]) (count1512 q) 1 1 (meaningNeg11 q) (meaningNeg13 q) (meaning1513 q) hs
  change (! (valuationOf q 11)) = false ∨ (! (valuationOf q 13)) = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 11 = true ∨ valuation q 13 = true ∨ valuation q 1513 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-9, -10]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -13])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-9, -10]) (countLit q [-11, -13]) (count1514 q) 1 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-9, -10]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -13])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1515)) (countLit q [-9, -10]) (countLit q [-11, -13]) (count1514 q) 2 (meaning1513 q) (meaning1515 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1515 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-9, -10]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-9, -10]) (countLit q [-11, -13]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-9, -10]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1515)) (countLit q [-9, -10]) (countLit q [-11, -13]) (count1514 q) 1 1 (meaning1510 q) (meaning1512 q) (meaning1515 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1512 = false ∨ valuation q 1515 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-9, -10]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1516)) (countLit q [-9, -10]) (countLit q [-11, -13]) (count1514 q) 1 2 (meaning1510 q) (meaning1513 q) (meaning1516 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1513 = false ∨ valuation q 1516 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-9, -10]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -13])
  have hm := merge_left (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-9, -10]) (countLit q [-11, -13]) (count1514 q) 2 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1516 = true := by
  have hs : count1514 q = (countLit q [-9, -10]) + (countLit q [-11, -13]) := List.countP_append (p := literal q) (l₁ := [-9, -10]) (l₂ := [-11, -13])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1516)) (countLit q [-9, -10]) (countLit q [-11, -13]) (count1514 q) 2 1 (meaning1511 q) (meaning1512 q) (meaning1516 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1512 = false ∨ valuation q 1516 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 1 (meaning1514 q) (meaning1518 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1518 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1515)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 2 (meaning1515 q) (meaning1519 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1519 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_right (literal (valuationOf q) (1516)) (literal (valuationOf q) (1520)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 3 (meaning1516 q) (meaning1520 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1520 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1518)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 1 (meaning1507 q) (meaning1518 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1518 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 1 1 (meaning1507 q) (meaning1514 q) (meaning1519 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1514 = false ∨ valuation q 1519 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1520)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 1 2 (meaning1507 q) (meaning1515 q) (meaning1520 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1515 = false ∨ valuation q 1520 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1521)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 1 3 (meaning1507 q) (meaning1516 q) (meaning1521 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1516 = false ∨ valuation q 1521 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1508)) (literal (valuationOf q) (1519)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 2 (meaning1508 q) (meaning1519 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1519 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1520)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 2 1 (meaning1508 q) (meaning1514 q) (meaning1520 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1514 = false ∨ valuation q 1520 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1521)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 2 2 (meaning1508 q) (meaning1515 q) (meaning1521 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1515 = false ∨ valuation q 1521 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1522)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 2 3 (meaning1508 q) (meaning1516 q) (meaning1522 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1516 = false ∨ valuation q 1522 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_left (literal (valuationOf q) (1509)) (literal (valuationOf q) (1520)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 3 (meaning1509 q) (meaning1520 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1520 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1521)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 3 1 (meaning1509 q) (meaning1514 q) (meaning1521 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1514 = false ∨ valuation q 1521 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true := by
  have hs : count1518 q = (countLit q [-2, -5, -8]) + (countLit q [-9, -10, -11, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8]) (l₂ := [-9, -10, -11, -13])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1522)) (countLit q [-2, -5, -8]) (countLit q [-9, -10, -11, -13]) (count1518 q) 3 2 (meaning1509 q) (meaning1515 q) (meaning1522 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1515 = false ∨ valuation q 1522 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (1525)) (countLit q [-14]) (countLit q [-15]) (count1525 q) 1 (meaningNeg15 q) (meaning1525 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1525 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 1525 = true := by
  have hs : count1525 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-14)) (literal (valuationOf q) (1525)) (countLit q [-14]) (countLit q [-15]) (count1525 q) 1 (meaningNeg14 q) (meaning1525 q) hs
  change (! (valuationOf q 14)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 1525 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 14 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-14]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-14]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-14)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1526)) (countLit q [-14]) (countLit q [-15]) (count1525 q) 1 1 (meaningNeg14 q) (meaningNeg15 q) (meaning1526 q) hs
  change (! (valuationOf q 14)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 14 = true ∨ valuation q 15 = true ∨ valuation q 1526 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1527 = true := by
  have hs : count1527 q = (countLit q [-18]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1527)) (countLit q [-18]) (countLit q [-22]) (count1527 q) 1 (meaningNeg22 q) (meaning1527 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1527 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1527 = true := by
  have hs : count1527 q = (countLit q [-18]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1527)) (countLit q [-18]) (countLit q [-22]) (count1527 q) 1 (meaningNeg18 q) (meaning1527 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1527 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1528 = true := by
  have hs : count1527 q = (countLit q [-18]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1528)) (countLit q [-18]) (countLit q [-22]) (count1527 q) 1 1 (meaningNeg18 q) (meaningNeg22 q) (meaning1528 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 22 = true ∨ valuation q 1528 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E089.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112089
