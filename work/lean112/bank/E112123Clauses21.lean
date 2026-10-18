import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-84]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1486)) (literal (valuationOf q) (1488)) (countLit q [-84]) (countLit q [-85, -86]) (count1487 q) 2 (meaning1486 q) (meaning1488 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1488 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1487 = true := by
  have hs : count1487 q = (countLit q [-84]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1487)) (countLit q [-84]) (countLit q [-85, -86]) (count1487 q) 1 (meaningNeg84 q) (meaning1487 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1487 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1487 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1485 = false ∨ valuationOf q 1488 = true := by
  have hs : count1487 q = (countLit q [-84]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (1485)) (literal (valuationOf q) (1488)) (countLit q [-84]) (countLit q [-85, -86]) (count1487 q) 1 1 (meaningNeg84 q) (meaning1485 q) (meaning1488 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1485 = false ∨ valuationOf q 1488 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1485 = false ∨ valuation q 1488 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1490)) (countLit q [-89]) (countLit q [-91]) (count1490 q) 1 (meaningNeg91 q) (meaning1490 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1490 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1490 = true := by
  have hs : count1490 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1490)) (countLit q [-89]) (countLit q [-91]) (count1490 q) 1 (meaningNeg89 q) (meaning1490 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1490 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1490 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1492 = true := by
  have hs : count1492 q = (countLit q [-93]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1492)) (countLit q [-93]) (countLit q [-96]) (count1492 q) 1 (meaningNeg96 q) (meaning1492 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1492 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1492 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-89, -91]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-89, -91]) (l₂ := [-93, -96])
  have hm := merge_right (literal (valuationOf q) (1492)) (literal (valuationOf q) (1494)) (countLit q [-89, -91]) (countLit q [-93, -96]) (count1494 q) 1 (meaning1492 q) (meaning1494 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1494 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1494 = true := by
  have hs : count1494 q = (countLit q [-89, -91]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-89, -91]) (l₂ := [-93, -96])
  have hm := merge_left (literal (valuationOf q) (1490)) (literal (valuationOf q) (1494)) (countLit q [-89, -91]) (countLit q [-93, -96]) (count1494 q) 1 (meaning1490 q) (meaning1494 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1494 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1494 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1495 = true := by
  have hs : count1494 q = (countLit q [-89, -91]) + (countLit q [-93, -96]) := List.countP_append (p := literal q) (l₁ := [-89, -91]) (l₂ := [-93, -96])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1492)) (literal (valuationOf q) (1495)) (countLit q [-89, -91]) (countLit q [-93, -96]) (count1494 q) 1 1 (meaning1490 q) (meaning1492 q) (meaning1495 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1492 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1492 = false ∨ valuation q 1495 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1499 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-89, -91, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-89, -91, -93, -96])
  have hm := merge_right (literal (valuationOf q) (1495)) (literal (valuationOf q) (1499)) (countLit q [-84, -85, -86]) (countLit q [-89, -91, -93, -96]) (count1498 q) 2 (meaning1495 q) (meaning1499 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1499 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1499 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-89, -91, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-89, -91, -93, -96])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1499)) (countLit q [-84, -85, -86]) (countLit q [-89, -91, -93, -96]) (count1498 q) 1 1 (meaning1487 q) (meaning1494 q) (meaning1499 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1494 = false ∨ valuation q 1499 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1499 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-89, -91, -93, -96]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-89, -91, -93, -96])
  have hm := merge_left (literal (valuationOf q) (1488)) (literal (valuationOf q) (1499)) (countLit q [-84, -85, -86]) (countLit q [-89, -91, -93, -96]) (count1498 q) 2 (meaning1488 q) (meaning1499 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1499 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-101]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-101])
  have hm := merge_right (literal (valuationOf q) (-101)) (literal (valuationOf q) (1505)) (countLit q [-99]) (countLit q [-101]) (count1505 q) 1 (meaningNeg101 q) (meaning1505 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1505 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-98]) (countLit q [-99, -101]) (count1507 q) 1 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-98]) + (countLit q [-99, -101]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99, -101])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1507)) (countLit q [-98]) (countLit q [-99, -101]) (count1507 q) 1 (meaningNeg98 q) (meaning1507 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1507 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1510)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 (meaningNeg106 q) (meaning1510 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1510 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1510)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 (meaningNeg104 q) (meaning1510 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1510 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -109]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -109])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-104, -106]) (countLit q [-107, -109]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1518)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 1 (meaning1514 q) (meaning1518 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1518 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-98, -99, -101]) + (countLit q [-104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-98, -99, -101]) (l₂ := [-104, -106, -107, -109])
  have hm := merge_left (literal (valuationOf q) (1507)) (literal (valuationOf q) (1518)) (countLit q [-98, -99, -101]) (countLit q [-104, -106, -107, -109]) (count1518 q) 1 (meaning1507 q) (meaning1518 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1518 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -89, -91, -93, -96]) + (countLit q [-98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -89, -91, -93, -96]) (l₂ := [-98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1527)) (countLit q [-84, -85, -86, -89, -91, -93, -96]) (countLit q [-98, -99, -101, -104, -106, -107, -109]) (count1525 q) 2 1 (meaning1499 q) (meaning1518 q) (meaning1527 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1518 = false ∨ valuation q 1527 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1543 = true := by
  have hs : count1538 q = (countLit q [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82]) + (countLit q [-84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82]) (l₂ := [-84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1543)) (countLit q [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82]) (countLit q [-84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109]) (count1538 q) 3 3 (meaning1474 q) (meaning1527 q) (meaning1543 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1527 = false ∨ valuation q 1543 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1544 = true := by
  have hs : count1538 q = (countLit q [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82]) + (countLit q [-84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82]) (l₂ := [-84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1475)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1544)) (countLit q [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82]) (countLit q [-84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109]) (count1538 q) 4 3 (meaning1475 q) (meaning1527 q) (meaning1544 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1527 = false ∨ valuation q 1544 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1563 = true := by
  have hs : count1551 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) + (countLit q [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82, -84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) (l₂ := [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82, -84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1428)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1563)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) (countLit q [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82, -84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109]) (count1551 q) 6 7 (meaning1428 q) (meaning1544 q) (meaning1563 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1544 = false ∨ valuation q 1563 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 1429 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1563 = true := by
  have hs : count1551 q = (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) + (countLit q [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82, -84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) (l₂ := [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82, -84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109])
  have hm := merge_two (literal (valuationOf q) (1429)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1563)) (countLit q [-2, -3, -7, -8, -10, -13, -14, -16, -19, -22, -23, -26, -28, -31, -34, -35, -37, -38, -40, -43, -44, -46, -49, -52, -53, -54]) (countLit q [-56, -58, -59, -61, -64, -66, -67, -69, -72, -74, -75, -78, -82, -84, -85, -86, -89, -91, -93, -96, -98, -99, -101, -104, -106, -107, -109]) (count1551 q) 7 6 (meaning1429 q) (meaning1543 q) (meaning1563 q) hs
  change valuationOf q 1429 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 1429 = false ∨ valuation q 1543 = false ∨ valuation q 1563 = true := counterClause697 (baseVal q)

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false := by
  rw [value1563]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1551 (baseVal q) = (oddSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_odd_bound q h
  rw [oddSide_length] at hb
  rw [he]
  omega

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 2 = false ∨ valuation q 10 = false ∨ valuation q 11 = false := by
  rw [value1, value2, value10, value11]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (1 : Vertex) (16 : Vertex) (17 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1 = false ∨ valuation q 3 = false ∨ valuation q 10 = false ∨ valuation q 12 = false := by
  rw [value1, value3, value10, value12]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (0 : Vertex) (2 : Vertex) (16 : Vertex) (18 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 12 = false ∨ valuation q 14 = false := by
  rw [value3, value6, value12, value14]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (2 : Vertex) (6 : Vertex) (18 : Vertex) (22 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 3 = false ∨ valuation q 6 = false ∨ valuation q 20 = false ∨ valuation q 23 = false := by
  rw [value3, value6, value20, value23]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (2 : Vertex) (6 : Vertex) (66 : Vertex) (70 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 8 = false ∨ valuation q 9 = false ∨ valuation q 17 = false ∨ valuation q 19 = false := by
  rw [value8, value9, value17, value19]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (13 : Vertex) (15 : Vertex) (29 : Vertex) (31 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 10 = false ∨ valuation q 11 = false ∨ valuation q 12 = false ∨ valuation q 13 = false := by
  rw [value10, value11, value12, value13]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  exact square_clause q (16 : Vertex) (17 : Vertex) (18 : Vertex) (19 : Vertex) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E123.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112123
