import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-79]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1459)) (countLit q [-79]) (countLit q [-82]) (count1459 q) 1 (meaningNeg79 q) (meaning1459 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1459 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-79]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1460)) (countLit q [-79]) (countLit q [-82]) (count1459 q) 1 1 (meaningNeg79 q) (meaningNeg82 q) (meaning1460 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 82 = true ∨ valuation q 1460 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-75, -76]) + (countLit q [-79, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -82])
  have hm := merge_right (literal (valuationOf q) (1459)) (literal (valuationOf q) (1461)) (countLit q [-75, -76]) (countLit q [-79, -82]) (count1461 q) 1 (meaning1459 q) (meaning1461 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1461 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1462 = true := by
  have hs : count1461 q = (countLit q [-75, -76]) + (countLit q [-79, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -82])
  have hm := merge_right (literal (valuationOf q) (1460)) (literal (valuationOf q) (1462)) (countLit q [-75, -76]) (countLit q [-79, -82]) (count1461 q) 2 (meaning1460 q) (meaning1462 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1462 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-75, -76]) + (countLit q [-79, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -82])
  have hm := merge_left (literal (valuationOf q) (1457)) (literal (valuationOf q) (1461)) (countLit q [-75, -76]) (countLit q [-79, -82]) (count1461 q) 1 (meaning1457 q) (meaning1461 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1461 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1462 = true := by
  have hs : count1461 q = (countLit q [-75, -76]) + (countLit q [-79, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -82])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1459)) (literal (valuationOf q) (1462)) (countLit q [-75, -76]) (countLit q [-79, -82]) (count1461 q) 1 1 (meaning1457 q) (meaning1459 q) (meaning1462 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1459 = false ∨ valuation q 1462 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1463 = true := by
  have hs : count1461 q = (countLit q [-75, -76]) + (countLit q [-79, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -82])
  have hm := merge_two (literal (valuationOf q) (1457)) (literal (valuationOf q) (1460)) (literal (valuationOf q) (1463)) (countLit q [-75, -76]) (countLit q [-79, -82]) (count1461 q) 1 2 (meaning1457 q) (meaning1460 q) (meaning1463 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1460 = false ∨ valuation q 1463 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1462 = true := by
  have hs : count1461 q = (countLit q [-75, -76]) + (countLit q [-79, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -82])
  have hm := merge_left (literal (valuationOf q) (1458)) (literal (valuationOf q) (1462)) (countLit q [-75, -76]) (countLit q [-79, -82]) (count1461 q) 2 (meaning1458 q) (meaning1462 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1462 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1463 = true := by
  have hs : count1461 q = (countLit q [-75, -76]) + (countLit q [-79, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -82])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1459)) (literal (valuationOf q) (1463)) (countLit q [-75, -76]) (countLit q [-79, -82]) (count1461 q) 2 1 (meaning1458 q) (meaning1459 q) (meaning1463 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1459 = false ∨ valuation q 1463 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1464 = true := by
  have hs : count1461 q = (countLit q [-75, -76]) + (countLit q [-79, -82]) := List.countP_append (p := literal q) (l₁ := [-75, -76]) (l₂ := [-79, -82])
  have hm := merge_two (literal (valuationOf q) (1458)) (literal (valuationOf q) (1460)) (literal (valuationOf q) (1464)) (countLit q [-75, -76]) (countLit q [-79, -82]) (count1461 q) 2 2 (meaning1458 q) (meaning1460 q) (meaning1464 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1460 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1460 = false ∨ valuation q 1464 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_right (literal (valuationOf q) (1461)) (literal (valuationOf q) (1465)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 1 (meaning1461 q) (meaning1465 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1465 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_right (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 2 (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1466 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 3 (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1467 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 4 (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1468 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_left (literal (valuationOf q) (1454)) (literal (valuationOf q) (1465)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 1 (meaning1454 q) (meaning1465 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1465 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1466)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 1 1 (meaning1454 q) (meaning1461 q) (meaning1466 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1461 = false ∨ valuation q 1466 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1467)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 1 2 (meaning1454 q) (meaning1462 q) (meaning1467 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1462 = false ∨ valuation q 1467 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1468 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1468)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 1 3 (meaning1454 q) (meaning1463 q) (meaning1468 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1463 = false ∨ valuation q 1468 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1469 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1454)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1469)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 1 4 (meaning1454 q) (meaning1464 q) (meaning1469 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1464 = false ∨ valuation q 1469 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_left (literal (valuationOf q) (1455)) (literal (valuationOf q) (1466)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 2 (meaning1455 q) (meaning1466 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1466 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1467)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 2 1 (meaning1455 q) (meaning1461 q) (meaning1467 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1461 = false ∨ valuation q 1467 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1468 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1462)) (literal (valuationOf q) (1468)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 2 2 (meaning1455 q) (meaning1462 q) (meaning1468 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1462 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1462 = false ∨ valuation q 1468 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1469 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1455)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1469)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 2 3 (meaning1455 q) (meaning1463 q) (meaning1469 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1463 = false ∨ valuation q 1469 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1468 = true := by
  have hs : count1465 q = (countLit q [-69, -73, -74]) + (countLit q [-75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-69, -73, -74]) (l₂ := [-75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1456)) (literal (valuationOf q) (1461)) (literal (valuationOf q) (1468)) (countLit q [-69, -73, -74]) (countLit q [-75, -76, -79, -82]) (count1465 q) 3 1 (meaning1456 q) (meaning1461 q) (meaning1468 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1461 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1461 = false ∨ valuation q 1468 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1472)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 1 (meaning1465 q) (meaning1472 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1472 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_right (literal (valuationOf q) (1466)) (literal (valuationOf q) (1473)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 2 (meaning1466 q) (meaning1473 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1473 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_right (literal (valuationOf q) (1467)) (literal (valuationOf q) (1474)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 3 (meaning1467 q) (meaning1474 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1474 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1475 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_right (literal (valuationOf q) (1468)) (literal (valuationOf q) (1475)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 4 (meaning1468 q) (meaning1475 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1475 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1476 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_right (literal (valuationOf q) (1469)) (literal (valuationOf q) (1476)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 5 (meaning1469 q) (meaning1476 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1476 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1473)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 1 1 (meaning1446 q) (meaning1465 q) (meaning1473 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1465 = false ∨ valuation q 1473 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1474)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 1 2 (meaning1446 q) (meaning1466 q) (meaning1474 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1466 = false ∨ valuation q 1474 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1475 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1475)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 1 3 (meaning1446 q) (meaning1467 q) (meaning1475 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1467 = false ∨ valuation q 1475 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E107.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112107
