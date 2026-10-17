import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1476 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1476)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 1 4 (meaning1446 q) (meaning1468 q) (meaning1476 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1468 = false ∨ valuation q 1476 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1477 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1469)) (literal (valuationOf q) (1477)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 1 5 (meaning1446 q) (meaning1469 q) (meaning1477 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1469 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1469 = false ∨ valuation q 1477 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1474 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1474)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 2 1 (meaning1447 q) (meaning1465 q) (meaning1474 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1465 = false ∨ valuation q 1474 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1475 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1475)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 2 2 (meaning1447 q) (meaning1466 q) (meaning1475 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1466 = false ∨ valuation q 1475 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1476 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1476)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 2 3 (meaning1447 q) (meaning1467 q) (meaning1476 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1467 = false ∨ valuation q 1476 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1477 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1477)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 2 4 (meaning1447 q) (meaning1468 q) (meaning1477 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1468 = false ∨ valuation q 1477 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1475 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1475)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 3 1 (meaning1448 q) (meaning1465 q) (meaning1475 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1465 = false ∨ valuation q 1475 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1476 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1476)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 3 2 (meaning1448 q) (meaning1466 q) (meaning1476 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1466 = false ∨ valuation q 1476 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1477 = true := by
  have hs : count1472 q = (countLit q [-56, -59, -60, -63, -66, -67]) + (countLit q [-69, -73, -74, -75, -76, -79, -82]) := List.countP_append (p := literal q) (l₁ := [-56, -59, -60, -63, -66, -67]) (l₂ := [-69, -73, -74, -75, -76, -79, -82])
  have hm := merge_two (literal (valuationOf q) (1448)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1477)) (countLit q [-56, -59, -60, -63, -66, -67]) (countLit q [-69, -73, -74, -75, -76, -79, -82]) (count1472 q) 3 3 (meaning1448 q) (meaning1467 q) (meaning1477 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1467 = false ∨ valuation q 1477 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1485)) (countLit q [-85]) (countLit q [-86]) (count1485 q) 1 (meaningNeg86 q) (meaning1485 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1485 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1485 = true := by
  have hs : count1485 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1485)) (countLit q [-85]) (countLit q [-86]) (count1485 q) 1 (meaningNeg85 q) (meaning1485 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1485 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1485 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1486 = true := by
  have hs : count1485 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1486)) (countLit q [-85]) (countLit q [-86]) (count1485 q) 1 1 (meaningNeg85 q) (meaningNeg86 q) (meaning1486 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1486 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 1486 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-84]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1485)) (literal (valuationOf q) (1487)) (countLit q [-84]) (countLit q [-85, -86]) (count1487 q) 1 (meaning1485 q) (meaning1487 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1487 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-84]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1486)) (literal (valuationOf q) (1488)) (countLit q [-84]) (countLit q [-85, -86]) (count1487 q) 2 (meaning1486 q) (meaning1488 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1488 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-84]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1487)) (countLit q [-84]) (countLit q [-85, -86]) (count1487 q) 1 (meaningNeg84 q) (meaning1487 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1487 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1485 = false ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-84]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1488)) (countLit q [-84]) (countLit q [-85, -86]) (count1487 q) 1 1 (meaningNeg84 q) (meaning1485 q) (meaning1488 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1485 = false ∨ valuation q 1488 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1490)) (countLit q [-88]) (countLit q [-90]) (count1490 q) 1 (meaningNeg90 q) (meaning1490 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1490 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1490)) (countLit q [-88]) (countLit q [-90]) (count1490 q) 1 (meaningNeg88 q) (meaning1490 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1490 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1491 = true := by
  have hs : count1490 q = (countLit q [-88]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1491)) (countLit q [-88]) (countLit q [-90]) (count1490 q) 1 1 (meaningNeg88 q) (meaningNeg90 q) (meaning1491 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1491 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 90 = true ∨ valuation q 1491 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1492)) (countLit q [-93]) (countLit q [-94]) (count1492 q) 1 (meaningNeg94 q) (meaning1492 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1492 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1492)) (countLit q [-93]) (countLit q [-94]) (count1492 q) 1 (meaningNeg93 q) (meaning1492 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1492 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1493 = true := by
  have hs : count1492 q = (countLit q [-93]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1493)) (countLit q [-93]) (countLit q [-94]) (count1492 q) 1 1 (meaningNeg93 q) (meaningNeg94 q) (meaning1493 q) hs
  change (! (valuationOf q 93)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1493 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 94 = true ∨ valuation q 1493 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-88, -90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1492)) (literal (valuationOf q) (1494)) (countLit q [-88, -90]) (countLit q [-93, -94]) (count1494 q) 1 (meaning1492 q) (meaning1494 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1494 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-88, -90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-93, -94])
  have hm := merge_right (literal (valuationOf q) (1493)) (literal (valuationOf q) (1495)) (countLit q [-88, -90]) (countLit q [-93, -94]) (count1494 q) 2 (meaning1493 q) (meaning1495 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1495 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-88, -90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-93, -94])
  have hm := merge_left (literal (valuationOf q) (1490)) (literal (valuationOf q) (1494)) (countLit q [-88, -90]) (countLit q [-93, -94]) (count1494 q) 1 (meaning1490 q) (meaning1494 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1494 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-88, -90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1495)) (countLit q [-88, -90]) (countLit q [-93, -94]) (count1494 q) 1 1 (meaning1490 q) (meaning1492 q) (meaning1495 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1492 = false ∨ valuation q 1495 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-88, -90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-93, -94])
  have hm := merge_left (literal (valuationOf q) (1491)) (literal (valuationOf q) (1495)) (countLit q [-88, -90]) (countLit q [-93, -94]) (count1494 q) 2 (meaning1491 q) (meaning1495 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1495 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1496 = true := by
  have hs : count1494 q = (countLit q [-88, -90]) + (countLit q [-93, -94]) := List.countP_append (p := literal q) (l₁ := [-88, -90]) (l₂ := [-93, -94])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1496)) (countLit q [-88, -90]) (countLit q [-93, -94]) (count1494 q) 2 1 (meaning1491 q) (meaning1492 q) (meaning1496 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1492 = false ∨ valuation q 1496 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1498 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-88, -90, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-88, -90, -93, -94])
  have hm := merge_right (literal (valuationOf q) (1494)) (literal (valuationOf q) (1498)) (countLit q [-84, -85, -86]) (countLit q [-88, -90, -93, -94]) (count1498 q) 1 (meaning1494 q) (meaning1498 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1498 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1499 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-88, -90, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-88, -90, -93, -94])
  have hm := merge_right (literal (valuationOf q) (1495)) (literal (valuationOf q) (1499)) (countLit q [-84, -85, -86]) (countLit q [-88, -90, -93, -94]) (count1498 q) 2 (meaning1495 q) (meaning1499 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1499 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1496 = false ∨ valuationOf q 1500 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-88, -90, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-88, -90, -93, -94])
  have hm := merge_right (literal (valuationOf q) (1496)) (literal (valuationOf q) (1500)) (countLit q [-84, -85, -86]) (countLit q [-88, -90, -93, -94]) (count1498 q) 3 (meaning1496 q) (meaning1500 q) hs
  change valuationOf q 1496 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1496 = false ∨ valuation q 1500 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1498 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-88, -90, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-88, -90, -93, -94])
  have hm := merge_left (literal (valuationOf q) (1487)) (literal (valuationOf q) (1498)) (countLit q [-84, -85, -86]) (countLit q [-88, -90, -93, -94]) (count1498 q) 1 (meaning1487 q) (meaning1498 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1498 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E107.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112107
