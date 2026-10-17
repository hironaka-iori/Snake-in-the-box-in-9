import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1426 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1455 = true := by
  have hs : count1449 q = (countLit q [-54, -55, -56, -58, -61, -63, -66]) + (countLit q [-68, -70, -71, -74, -75, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -56, -58, -61, -63, -66]) (l₂ := [-68, -70, -71, -74, -75, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1426)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1455)) (countLit q [-54, -55, -56, -58, -61, -63, -66]) (countLit q [-68, -70, -71, -74, -75, -78, -80]) (count1449 q) 5 2 (meaning1426 q) (meaning1443 q) (meaning1455 q) hs
  change valuationOf q 1426 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1426 = false ∨ valuation q 1443 = false ∨ valuation q 1455 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1463)) (countLit q [-85]) (countLit q [-87]) (count1463 q) 1 (meaningNeg87 q) (meaning1463 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1463 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1463)) (countLit q [-85]) (countLit q [-87]) (count1463 q) 1 (meaningNeg85 q) (meaning1463 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1463 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1464)) (countLit q [-85]) (countLit q [-87]) (count1463 q) 1 1 (meaningNeg85 q) (meaningNeg87 q) (meaning1464 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 87 = true ∨ valuation q 1464 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-83]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85, -87])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (countLit q [-83]) (countLit q [-85, -87]) (count1465 q) 1 (meaning1463 q) (meaning1465 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-83]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85, -87])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-83]) (countLit q [-85, -87]) (count1465 q) 2 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-83]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85, -87])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1465)) (countLit q [-83]) (countLit q [-85, -87]) (count1465 q) 1 (meaningNeg83 q) (meaning1465 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1465 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-83]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85, -87])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (countLit q [-83]) (countLit q [-85, -87]) (count1465 q) 1 1 (meaningNeg83 q) (meaning1463 q) (meaning1466 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1463 = false ∨ valuation q 1466 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-83]) + (countLit q [-85, -87]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85, -87])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-83]) (countLit q [-85, -87]) (count1465 q) 1 2 (meaningNeg83 q) (meaning1464 q) (meaning1467 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1468)) (countLit q [-88]) (countLit q [-91]) (count1468 q) 1 (meaningNeg91 q) (meaning1468 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1468 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1468 = true := by
  have hs : count1468 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1468)) (countLit q [-88]) (countLit q [-91]) (count1468 q) 1 (meaningNeg88 q) (meaning1468 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1468 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1469 = true := by
  have hs : count1468 q = (countLit q [-88]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1469)) (countLit q [-88]) (countLit q [-91]) (count1468 q) 1 1 (meaningNeg88 q) (meaningNeg91 q) (meaning1469 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 91 = true ∨ valuation q 1469 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-92]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1470)) (countLit q [-92]) (countLit q [-94]) (count1470 q) 1 (meaningNeg94 q) (meaning1470 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1470 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-92]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1470)) (countLit q [-92]) (countLit q [-94]) (count1470 q) 1 (meaningNeg92 q) (meaning1470 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1470 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-92]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1471)) (countLit q [-92]) (countLit q [-94]) (count1470 q) 1 1 (meaningNeg92 q) (meaningNeg94 q) (meaning1471 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 94 = true ∨ valuation q 1471 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-88, -91]) + (countLit q [-92, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -94])
  have hm := merge_right (literal (valuationOf q) (1470)) (literal (valuationOf q) (1472)) (countLit q [-88, -91]) (countLit q [-92, -94]) (count1472 q) 1 (meaning1470 q) (meaning1472 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1472 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-88, -91]) + (countLit q [-92, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -94])
  have hm := merge_right (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (countLit q [-88, -91]) (countLit q [-92, -94]) (count1472 q) 2 (meaning1471 q) (meaning1473 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-88, -91]) + (countLit q [-92, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -94])
  have hm := merge_left (literal (valuationOf q) (1468)) (literal (valuationOf q) (1472)) (countLit q [-88, -91]) (countLit q [-92, -94]) (count1472 q) 1 (meaning1468 q) (meaning1472 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1472 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-88, -91]) + (countLit q [-92, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -94])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1473)) (countLit q [-88, -91]) (countLit q [-92, -94]) (count1472 q) 1 1 (meaning1468 q) (meaning1470 q) (meaning1473 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1470 = false ∨ valuation q 1473 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-88, -91]) + (countLit q [-92, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -94])
  have hm := merge_two (literal (valuationOf q) (1468)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1474)) (countLit q [-88, -91]) (countLit q [-92, -94]) (count1472 q) 1 2 (meaning1468 q) (meaning1471 q) (meaning1474 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1471 = false ∨ valuation q 1474 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-88, -91]) + (countLit q [-92, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -94])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1470)) (literal (valuationOf q) (1474)) (countLit q [-88, -91]) (countLit q [-92, -94]) (count1472 q) 2 1 (meaning1469 q) (meaning1470 q) (meaning1474 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1470 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1470 = false ∨ valuation q 1474 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1475 = true := by
  have hs : count1472 q = (countLit q [-88, -91]) + (countLit q [-92, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -91]) (l₂ := [-92, -94])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1475)) (countLit q [-88, -91]) (countLit q [-92, -94]) (count1472 q) 2 2 (meaning1469 q) (meaning1471 q) (meaning1475 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1471 = false ∨ valuation q 1475 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 1 (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1476 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1477)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 2 (meaning1473 q) (meaning1477 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1477 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 3 (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1479)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 4 (meaning1475 q) (meaning1479 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1479 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1476 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_left (literal (valuationOf q) (1465)) (literal (valuationOf q) (1476)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 1 (meaning1465 q) (meaning1476 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1476 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1477)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 1 1 (meaning1465 q) (meaning1472 q) (meaning1477 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1472 = false ∨ valuation q 1477 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1478)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 1 2 (meaning1465 q) (meaning1473 q) (meaning1478 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1473 = false ∨ valuation q 1478 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_two (literal (valuationOf q) (1465)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1479)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 1 3 (meaning1465 q) (meaning1474 q) (meaning1479 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1474 = false ∨ valuation q 1479 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1477 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_left (literal (valuationOf q) (1466)) (literal (valuationOf q) (1477)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 2 (meaning1466 q) (meaning1477 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1477 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1478 = true := by
  have hs : count1476 q = (countLit q [-83, -85, -87]) + (countLit q [-88, -91, -92, -94]) := List.countP_append (p := literal q) (l₁ := [-83, -85, -87]) (l₂ := [-88, -91, -92, -94])
  have hm := merge_two (literal (valuationOf q) (1466)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1478)) (countLit q [-83, -85, -87]) (countLit q [-88, -91, -92, -94]) (count1476 q) 2 1 (meaning1466 q) (meaning1472 q) (meaning1478 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1472 = false ∨ valuation q 1478 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E090.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112090
