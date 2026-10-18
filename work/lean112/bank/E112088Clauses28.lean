import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1492 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1492)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 6 4 (meaning1457 q) (meaning1478 q) (meaning1492 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1478 = false ∨ valuation q 1492 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1493 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1493)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 6 5 (meaning1457 q) (meaning1479 q) (meaning1493 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1479 = false ∨ valuation q 1493 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1490 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1490)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 7 1 (meaning1458 q) (meaning1475 q) (meaning1490 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1475 = false ∨ valuation q 1490 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1491 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1491)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 7 2 (meaning1458 q) (meaning1476 q) (meaning1491 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1476 = false ∨ valuation q 1491 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1492 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1492)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 7 3 (meaning1458 q) (meaning1477 q) (meaning1492 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1477 = false ∨ valuation q 1492 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1493 = true := by
  have hs : count1483 q = (countLit q [-29, -32, -33, -35, -36, -39, -40]) + (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-29, -32, -33, -35, -36, -39, -40]) (l₂ := [-42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1493)) (countLit q [-29, -32, -33, -35, -36, -39, -40]) (countLit q [-42, -45, -47, -48, -51, -55, -56, -57]) (count1483 q) 7 4 (meaning1458 q) (meaning1478 q) (meaning1493 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1478 = false ∨ valuation q 1493 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1506 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_right (literal (valuationOf q) (1491)) (literal (valuationOf q) (1506)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 9 (meaning1491 q) (meaning1506 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1506 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1505 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1505)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 1 7 (meaning1425 q) (meaning1489 q) (meaning1505 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1489 = false ∨ valuation q 1505 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1506 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1506)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 1 8 (meaning1425 q) (meaning1490 q) (meaning1506 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1490 = false ∨ valuation q 1506 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1507 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1507)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 1 9 (meaning1425 q) (meaning1491 q) (meaning1507 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1491 = false ∨ valuation q 1507 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1508 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1508)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 1 10 (meaning1425 q) (meaning1492 q) (meaning1508 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1492 = false ∨ valuation q 1508 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1509 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1509)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 1 11 (meaning1425 q) (meaning1493 q) (meaning1509 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1493 = false ∨ valuation q 1509 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1505 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1505)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 2 6 (meaning1426 q) (meaning1488 q) (meaning1505 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1488 = false ∨ valuation q 1505 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1506 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1506)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 2 7 (meaning1426 q) (meaning1489 q) (meaning1506 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1489 = false ∨ valuation q 1506 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1507 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1507)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 2 8 (meaning1426 q) (meaning1490 q) (meaning1507 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1490 = false ∨ valuation q 1507 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1508 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1508)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 2 9 (meaning1426 q) (meaning1491 q) (meaning1508 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1491 = false ∨ valuation q 1508 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1509 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1509)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 2 10 (meaning1426 q) (meaning1492 q) (meaning1509 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1492 = false ∨ valuation q 1509 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1510 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1510)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 2 11 (meaning1426 q) (meaning1493 q) (meaning1510 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1493 = false ∨ valuation q 1510 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1504 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1486)) (literal (valuationOf q) (1504)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 3 4 (meaning1427 q) (meaning1486 q) (meaning1504 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1486 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1486 = false ∨ valuation q 1504 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1505 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1505)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 3 5 (meaning1427 q) (meaning1487 q) (meaning1505 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1487 = false ∨ valuation q 1505 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1506 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1506)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 3 6 (meaning1427 q) (meaning1488 q) (meaning1506 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1488 = false ∨ valuation q 1506 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1507 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1507)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 3 7 (meaning1427 q) (meaning1489 q) (meaning1507 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1489 = false ∨ valuation q 1507 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1508 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1508)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 3 8 (meaning1427 q) (meaning1490 q) (meaning1508 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1490 = false ∨ valuation q 1508 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1509 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1509)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 3 9 (meaning1427 q) (meaning1491 q) (meaning1509 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1491 = false ∨ valuation q 1509 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1510 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1510)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 3 10 (meaning1427 q) (meaning1492 q) (meaning1510 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1492 = false ∨ valuation q 1510 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1506 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1487)) (literal (valuationOf q) (1506)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 4 5 (meaning1428 q) (meaning1487 q) (meaning1506 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1487 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1487 = false ∨ valuation q 1506 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1507 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1488)) (literal (valuationOf q) (1507)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 4 6 (meaning1428 q) (meaning1488 q) (meaning1507 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1488 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1488 = false ∨ valuation q 1507 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1508 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1508)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 4 7 (meaning1428 q) (meaning1489 q) (meaning1508 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1489 = false ∨ valuation q 1508 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1509 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1509)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 4 8 (meaning1428 q) (meaning1490 q) (meaning1509 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1490 = false ∨ valuation q 1509 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1510 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1510)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 4 9 (meaning1428 q) (meaning1491 q) (meaning1510 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1491 = false ∨ valuation q 1510 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1512 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1512)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 4 11 (meaning1428 q) (meaning1493 q) (meaning1512 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1493 = false ∨ valuation q 1512 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1505 = true := by
  have hs : count1498 q = (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) + (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (l₂ := [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1505)) (countLit q [-3, -5, -6, -8, -9, -13, -16, -19, -20, -21, -23, -25, -27, -28]) (countLit q [-29, -32, -33, -35, -36, -39, -40, -42, -45, -47, -48, -51, -55, -56, -57]) (count1498 q) 5 3 (meaning1429 q) (meaning1485 q) (meaning1505 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1485 = false ∨ valuation q 1505 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E088.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112088
