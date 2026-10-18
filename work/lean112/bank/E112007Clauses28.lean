import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1482)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 2 3 (meaning1468 q) (meaning1476 q) (meaning1482 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1476 = false ∨ valuation q 1482 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1469)) (literal (valuationOf q) (1480)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 3 (meaning1469 q) (meaning1480 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1480 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1481)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 3 1 (meaning1469 q) (meaning1474 q) (meaning1481 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1474 = false ∨ valuation q 1481 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1475)) (literal (valuationOf q) (1482)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 3 2 (meaning1469 q) (meaning1475 q) (meaning1482 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1475 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1475 = false ∨ valuation q 1482 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1478 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1478)) (literal (valuationOf q) (1485)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 (meaning1478 q) (meaning1485 q) hs
  change valuationOf q 1478 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1478 = false ∨ valuation q 1485 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1479 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1479)) (literal (valuationOf q) (1486)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 (meaning1479 q) (meaning1486 q) hs
  change valuationOf q 1479 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1479 = false ∨ valuation q 1486 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1480 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1480)) (literal (valuationOf q) (1487)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 (meaning1480 q) (meaning1487 q) hs
  change valuationOf q 1480 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1480 = false ∨ valuation q 1487 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1481 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1481)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 (meaning1481 q) (meaning1488 q) hs
  change valuationOf q 1481 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1481 = false ∨ valuation q 1488 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1482)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 5 (meaning1482 q) (meaning1489 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1489 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1458)) (literal (valuationOf q) (1485)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 (meaning1458 q) (meaning1485 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1485 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1486)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 1 (meaning1458 q) (meaning1478 q) (meaning1486 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1478 = false ∨ valuation q 1486 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1487)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 2 (meaning1458 q) (meaning1479 q) (meaning1487 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1479 = false ∨ valuation q 1487 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 3 (meaning1458 q) (meaning1480 q) (meaning1488 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1480 = false ∨ valuation q 1488 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 1 4 (meaning1458 q) (meaning1481 q) (meaning1489 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1481 = false ∨ valuation q 1489 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1459)) (literal (valuationOf q) (1486)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 (meaning1459 q) (meaning1486 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1486 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1487)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 1 (meaning1459 q) (meaning1478 q) (meaning1487 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1478 = false ∨ valuation q 1487 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 2 (meaning1459 q) (meaning1479 q) (meaning1488 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1479 = false ∨ valuation q 1488 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 3 (meaning1459 q) (meaning1480 q) (meaning1489 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1480 = false ∨ valuation q 1489 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 2 4 (meaning1459 q) (meaning1481 q) (meaning1490 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1481 = false ∨ valuation q 1490 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1487 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1487)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 (meaning1460 q) (meaning1487 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1487 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 1 (meaning1460 q) (meaning1478 q) (meaning1488 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1478 = false ∨ valuation q 1488 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 2 (meaning1460 q) (meaning1479 q) (meaning1489 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1479 = false ∨ valuation q 1489 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 3 3 (meaning1460 q) (meaning1480 q) (meaning1490 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1480 = false ∨ valuation q 1490 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1488 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1461)) (literal (valuationOf q) (1488)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 (meaning1461 q) (meaning1488 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1488 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1489)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 1 (meaning1461 q) (meaning1478 q) (meaning1489 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1478 = false ∨ valuation q 1489 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1479)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 4 2 (meaning1461 q) (meaning1479 q) (meaning1490 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1479 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1479 = false ∨ valuation q 1490 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true := by
  have hs : count1485 q = (countLit q [-3, -5, -7, -11, -12, -14, -17]) + (countLit q [-20, -21, -23, -25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17]) (l₂ := [-20, -21, -23, -25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1490)) (countLit q [-3, -5, -7, -11, -12, -14, -17]) (countLit q [-20, -21, -23, -25, -26, -28, -31]) (count1485 q) 5 1 (meaning1462 q) (meaning1478 q) (meaning1490 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1478 = false ∨ valuation q 1490 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (1499)) (countLit q [-36]) (countLit q [-37]) (count1499 q) 1 (meaningNeg37 q) (meaning1499 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 1499 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1499 = true := by
  have hs : count1499 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1499)) (countLit q [-36]) (countLit q [-37]) (count1499 q) 1 (meaningNeg36 q) (meaning1499 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1499 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 37 = true ∨ valuationOf q 1500 = true := by
  have hs : count1499 q = (countLit q [-36]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (1500)) (countLit q [-36]) (countLit q [-37]) (count1499 q) 1 1 (meaningNeg36 q) (meaningNeg37 q) (meaning1500 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 37 = true ∨ valuation q 1500 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36, -37])
  have hm := merge_right (literal (valuationOf q) (1499)) (literal (valuationOf q) (1501)) (countLit q [-34]) (countLit q [-36, -37]) (count1501 q) 1 (meaning1499 q) (meaning1501 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1501 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-36, -37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36, -37])
  have hm := merge_right (literal (valuationOf q) (1500)) (literal (valuationOf q) (1502)) (countLit q [-34]) (countLit q [-36, -37]) (count1501 q) 2 (meaning1500 q) (meaning1502 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1502 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E007.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112007
