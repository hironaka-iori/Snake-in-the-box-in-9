import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-17, -21, -23]) + (countLit q [-24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -21, -23]) (l₂ := [-24, -25, -29, -31])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1481)) (countLit q [-17, -21, -23]) (countLit q [-24, -25, -29, -31]) (count1480 q) 2 (meaning1477 q) (meaning1481 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1481 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1480 = true := by
  have hs : count1480 q = (countLit q [-17, -21, -23]) + (countLit q [-24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -21, -23]) (l₂ := [-24, -25, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1469)) (literal (valuationOf q) (1480)) (countLit q [-17, -21, -23]) (countLit q [-24, -25, -29, -31]) (count1480 q) 1 (meaning1469 q) (meaning1480 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1480 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true := by
  have hs : count1480 q = (countLit q [-17, -21, -23]) + (countLit q [-24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -21, -23]) (l₂ := [-24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1481)) (countLit q [-17, -21, -23]) (countLit q [-24, -25, -29, -31]) (count1480 q) 1 1 (meaning1469 q) (meaning1476 q) (meaning1481 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1476 = false ∨ valuation q 1481 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1482 = true := by
  have hs : count1480 q = (countLit q [-17, -21, -23]) + (countLit q [-24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -21, -23]) (l₂ := [-24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1482)) (countLit q [-17, -21, -23]) (countLit q [-24, -25, -29, -31]) (count1480 q) 1 2 (meaning1469 q) (meaning1477 q) (meaning1482 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1477 = false ∨ valuation q 1482 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true := by
  have hs : count1480 q = (countLit q [-17, -21, -23]) + (countLit q [-24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -21, -23]) (l₂ := [-24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1478)) (literal (valuationOf q) (1483)) (countLit q [-17, -21, -23]) (countLit q [-24, -25, -29, -31]) (count1480 q) 1 3 (meaning1469 q) (meaning1478 q) (meaning1483 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1478 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1478 = false ∨ valuation q 1483 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true := by
  have hs : count1480 q = (countLit q [-17, -21, -23]) + (countLit q [-24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -21, -23]) (l₂ := [-24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1476)) (literal (valuationOf q) (1482)) (countLit q [-17, -21, -23]) (countLit q [-24, -25, -29, -31]) (count1480 q) 2 1 (meaning1470 q) (meaning1476 q) (meaning1482 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1476 = false ∨ valuationOf q 1482 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1476 = false ∨ valuation q 1482 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1483 = true := by
  have hs : count1480 q = (countLit q [-17, -21, -23]) + (countLit q [-24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-17, -21, -23]) (l₂ := [-24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1477)) (literal (valuationOf q) (1483)) (countLit q [-17, -21, -23]) (countLit q [-24, -25, -29, -31]) (count1480 q) 2 2 (meaning1470 q) (meaning1477 q) (meaning1483 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1477 = false ∨ valuationOf q 1483 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1477 = false ∨ valuation q 1483 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -6, -10, -11, -12, -13]) + (countLit q [-17, -21, -23, -24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13]) (l₂ := [-17, -21, -23, -24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1488)) (countLit q [-2, -4, -6, -10, -11, -12, -13]) (countLit q [-17, -21, -23, -24, -25, -29, -31]) (count1487 q) 1 1 (meaning1460 q) (meaning1480 q) (meaning1488 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1480 = false ∨ valuation q 1488 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1489 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -6, -10, -11, -12, -13]) + (countLit q [-17, -21, -23, -24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13]) (l₂ := [-17, -21, -23, -24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1489)) (countLit q [-2, -4, -6, -10, -11, -12, -13]) (countLit q [-17, -21, -23, -24, -25, -29, -31]) (count1487 q) 1 2 (meaning1460 q) (meaning1481 q) (meaning1489 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1481 = false ∨ valuation q 1489 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1490 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -6, -10, -11, -12, -13]) + (countLit q [-17, -21, -23, -24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13]) (l₂ := [-17, -21, -23, -24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -6, -10, -11, -12, -13]) (countLit q [-17, -21, -23, -24, -25, -29, -31]) (count1487 q) 1 3 (meaning1460 q) (meaning1482 q) (meaning1490 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1482 = false ∨ valuation q 1490 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -6, -10, -11, -12, -13]) + (countLit q [-17, -21, -23, -24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13]) (l₂ := [-17, -21, -23, -24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1460)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1491)) (countLit q [-2, -4, -6, -10, -11, -12, -13]) (countLit q [-17, -21, -23, -24, -25, -29, -31]) (count1487 q) 1 4 (meaning1460 q) (meaning1483 q) (meaning1491 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1483 = false ∨ valuation q 1491 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -6, -10, -11, -12, -13]) + (countLit q [-17, -21, -23, -24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13]) (l₂ := [-17, -21, -23, -24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1480)) (literal (valuationOf q) (1489)) (countLit q [-2, -4, -6, -10, -11, -12, -13]) (countLit q [-17, -21, -23, -24, -25, -29, -31]) (count1487 q) 2 1 (meaning1461 q) (meaning1480 q) (meaning1489 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1480 = false ∨ valuationOf q 1489 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1480 = false ∨ valuation q 1489 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -6, -10, -11, -12, -13]) + (countLit q [-17, -21, -23, -24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13]) (l₂ := [-17, -21, -23, -24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1481)) (literal (valuationOf q) (1490)) (countLit q [-2, -4, -6, -10, -11, -12, -13]) (countLit q [-17, -21, -23, -24, -25, -29, -31]) (count1487 q) 2 2 (meaning1461 q) (meaning1481 q) (meaning1490 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1481 = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1481 = false ∨ valuation q 1490 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -6, -10, -11, -12, -13]) + (countLit q [-17, -21, -23, -24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13]) (l₂ := [-17, -21, -23, -24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1482)) (literal (valuationOf q) (1491)) (countLit q [-2, -4, -6, -10, -11, -12, -13]) (countLit q [-17, -21, -23, -24, -25, -29, -31]) (count1487 q) 2 3 (meaning1461 q) (meaning1482 q) (meaning1491 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1482 = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1482 = false ∨ valuation q 1491 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true := by
  have hs : count1487 q = (countLit q [-2, -4, -6, -10, -11, -12, -13]) + (countLit q [-17, -21, -23, -24, -25, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13]) (l₂ := [-17, -21, -23, -24, -25, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1483)) (literal (valuationOf q) (1492)) (countLit q [-2, -4, -6, -10, -11, -12, -13]) (countLit q [-17, -21, -23, -24, -25, -29, -31]) (count1487 q) 2 4 (meaning1461 q) (meaning1483 q) (meaning1492 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1483 = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1483 = false ∨ valuation q 1492 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_right (literal (valuationOf q) (-35)) (literal (valuationOf q) (1501)) (countLit q [-34]) (countLit q [-35]) (count1501 q) 1 (meaningNeg35 q) (meaning1501 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 1501 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1501 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1501)) (countLit q [-34]) (countLit q [-35]) (count1501 q) 1 (meaningNeg34 q) (meaning1501 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1501 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 35 = true ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-34]) + (countLit q [-35]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-35])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-35)) (literal (valuationOf q) (1502)) (countLit q [-34]) (countLit q [-35]) (count1501 q) 1 1 (meaningNeg34 q) (meaningNeg35 q) (meaning1502 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 35)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 35 = true ∨ valuation q 1502 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1503)) (countLit q [-32]) (countLit q [-34, -35]) (count1503 q) 1 (meaning1501 q) (meaning1503 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1503 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_right (literal (valuationOf q) (1502)) (literal (valuationOf q) (1504)) (countLit q [-32]) (countLit q [-34, -35]) (count1503 q) 2 (meaning1502 q) (meaning1504 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1504 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1503)) (countLit q [-32]) (countLit q [-34, -35]) (count1503 q) 1 (meaningNeg32 q) (meaning1503 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1503 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1504)) (countLit q [-32]) (countLit q [-34, -35]) (count1503 q) 1 1 (meaningNeg32 q) (meaning1501 q) (meaning1504 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1501 = false ∨ valuation q 1504 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true := by
  have hs : count1503 q = (countLit q [-32]) + (countLit q [-34, -35]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -35])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1502)) (literal (valuationOf q) (1505)) (countLit q [-32]) (countLit q [-34, -35]) (count1503 q) 1 2 (meaningNeg32 q) (meaning1502 q) (meaning1505 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1502 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1502 = false ∨ valuation q 1505 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (1506)) (countLit q [-39]) (countLit q [-40]) (count1506 q) 1 (meaningNeg40 q) (meaning1506 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1506 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1506 = true := by
  have hs : count1506 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (1506)) (countLit q [-39]) (countLit q [-40]) (count1506 q) 1 (meaningNeg39 q) (meaning1506 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1506 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 40 = true ∨ valuationOf q 1507 = true := by
  have hs : count1506 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (1507)) (countLit q [-39]) (countLit q [-40]) (count1506 q) 1 1 (meaningNeg39 q) (meaningNeg40 q) (meaning1507 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 1507 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (1508)) (countLit q [-41]) (countLit q [-42]) (count1508 q) 1 (meaningNeg42 q) (meaning1508 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1508 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1508 = true := by
  have hs : count1508 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (1508)) (countLit q [-41]) (countLit q [-42]) (count1508 q) 1 (meaningNeg41 q) (meaning1508 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1508 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 42 = true ∨ valuationOf q 1509 = true := by
  have hs : count1508 q = (countLit q [-41]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (1509)) (countLit q [-41]) (countLit q [-42]) (count1508 q) 1 1 (meaningNeg41 q) (meaningNeg42 q) (meaning1509 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 42 = true ∨ valuation q 1509 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-39, -40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-39, -40]) (l₂ := [-41, -42])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1510)) (countLit q [-39, -40]) (countLit q [-41, -42]) (count1510 q) 1 (meaning1508 q) (meaning1510 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1510 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-39, -40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-39, -40]) (l₂ := [-41, -42])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1511)) (countLit q [-39, -40]) (countLit q [-41, -42]) (count1510 q) 2 (meaning1509 q) (meaning1511 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1511 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-39, -40]) + (countLit q [-41, -42]) := List.countP_append (p := literal q) (l₁ := [-39, -40]) (l₂ := [-41, -42])
  have hm := merge_left (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-39, -40]) (countLit q [-41, -42]) (count1510 q) 1 (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1510 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E187.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112187
