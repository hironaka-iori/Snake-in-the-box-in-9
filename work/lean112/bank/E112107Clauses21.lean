import E112107Semantics
import B112E107Inputs
namespace Snake9.Regrowth.E112107
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1499 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-88, -90, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-88, -90, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1499)) (countLit q [-84, -85, -86]) (countLit q [-88, -90, -93, -94]) (count1498 q) 1 1 (meaning1487 q) (meaning1494 q) (meaning1499 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1494 = false ∨ valuation q 1499 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1500 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-88, -90, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-88, -90, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1500)) (countLit q [-84, -85, -86]) (countLit q [-88, -90, -93, -94]) (count1498 q) 1 2 (meaning1487 q) (meaning1495 q) (meaning1500 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1495 = false ∨ valuation q 1500 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-88, -90, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-88, -90, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1501)) (countLit q [-84, -85, -86]) (countLit q [-88, -90, -93, -94]) (count1498 q) 1 3 (meaning1487 q) (meaning1496 q) (meaning1501 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1501 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1496 = false ∨ valuation q 1501 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1499 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-88, -90, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-88, -90, -93, -94])
  have hm := merge_left (literal (valuationOf q) (1488)) (literal (valuationOf q) (1499)) (countLit q [-84, -85, -86]) (countLit q [-88, -90, -93, -94]) (count1498 q) 2 (meaning1488 q) (meaning1499 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1499 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1499 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1500 = true := by
  have hs : count1498 q = (countLit q [-84, -85, -86]) + (countLit q [-88, -90, -93, -94]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86]) (l₂ := [-88, -90, -93, -94])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1500)) (countLit q [-84, -85, -86]) (countLit q [-88, -90, -93, -94]) (count1498 q) 2 1 (meaning1488 q) (meaning1494 q) (meaning1500 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1500 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1494 = false ∨ valuation q 1500 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1505)) (countLit q [-99]) (countLit q [-102]) (count1505 q) 1 (meaningNeg102 q) (meaning1505 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1505 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1505)) (countLit q [-99]) (countLit q [-102]) (count1505 q) 1 (meaningNeg99 q) (meaning1505 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1505 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 102 = true ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-99]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-102])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-102)) (literal (valuationOf q) (1506)) (countLit q [-99]) (countLit q [-102]) (count1505 q) 1 1 (meaningNeg99 q) (meaningNeg102 q) (meaning1506 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 102)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 102 = true ∨ valuation q 1506 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-97]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99, -102])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-97]) (countLit q [-99, -102]) (count1507 q) 1 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-97]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99, -102])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (countLit q [-97]) (countLit q [-99, -102]) (count1507 q) 2 (meaning1506 q) (meaning1508 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-97]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99, -102])
  have hm := merge_left (literal (valuationOf q) (-97)) (literal (valuationOf q) (1507)) (countLit q [-97]) (countLit q [-99, -102]) (count1507 q) 1 (meaningNeg97 q) (meaning1507 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1507 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-97]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99, -102])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-97]) (countLit q [-99, -102]) (count1507 q) 1 1 (meaningNeg97 q) (meaning1505 q) (meaning1508 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-97]) + (countLit q [-99, -102]) := List.countP_append (p := literal q) (l₁ := [-97]) (l₂ := [-99, -102])
  have hm := merge_two (literal (valuationOf q) (-97)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (countLit q [-97]) (countLit q [-99, -102]) (count1507 q) 1 2 (meaningNeg97 q) (meaning1506 q) (meaning1509 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1506 = false ∨ valuation q 1509 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 106 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_right (literal (valuationOf q) (-106)) (literal (valuationOf q) (1510)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 (meaningNeg106 q) (meaning1510 q) hs
  change (! (valuationOf q 106)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 106 = true ∨ valuation q 1510 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1510 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_left (literal (valuationOf q) (-104)) (literal (valuationOf q) (1510)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 (meaningNeg104 q) (meaning1510 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1510 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 106 = true ∨ valuationOf q 1511 = true := by
  have hs : count1510 q = (countLit q [-104]) + (countLit q [-106]) := List.countP_append (p := literal q) (l₁ := [-104]) (l₂ := [-106])
  have hm := merge_two (literal (valuationOf q) (-104)) (literal (valuationOf q) (-106)) (literal (valuationOf q) (1511)) (countLit q [-104]) (countLit q [-106]) (count1510 q) 1 1 (meaningNeg104 q) (meaningNeg106 q) (meaning1511 q) hs
  change (! (valuationOf q 104)) = false ∨ (! (valuationOf q 106)) = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 106 = true ∨ valuation q 1511 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1512)) (countLit q [-107]) (countLit q [-108]) (count1512 q) 1 (meaningNeg108 q) (meaning1512 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1512 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1512)) (countLit q [-107]) (countLit q [-108]) (count1512 q) 1 (meaningNeg107 q) (meaning1512 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1512 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -108])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1514)) (countLit q [-104, -106]) (countLit q [-107, -108]) (count1514 q) 1 (meaning1512 q) (meaning1514 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1514 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-104, -106]) (countLit q [-107, -108]) (count1514 q) 1 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -108])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1515)) (countLit q [-104, -106]) (countLit q [-107, -108]) (count1514 q) 1 1 (meaning1510 q) (meaning1512 q) (meaning1515 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1512 = false ∨ valuation q 1515 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1514 q = (countLit q [-104, -106]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-104, -106]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-104, -106]) (countLit q [-107, -108]) (count1514 q) 2 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1518 = true := by
  have hs : count1518 q = (countLit q [-97, -99, -102]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-97, -99, -102]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1518)) (countLit q [-97, -99, -102]) (countLit q [-104, -106, -107, -108]) (count1518 q) 1 (meaning1514 q) (meaning1518 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1518 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-97, -99, -102]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-97, -99, -102]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_right (literal (valuationOf q) (1515)) (literal (valuationOf q) (1519)) (countLit q [-97, -99, -102]) (countLit q [-104, -106, -107, -108]) (count1518 q) 2 (meaning1515 q) (meaning1519 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1519 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true := by
  have hs : count1518 q = (countLit q [-97, -99, -102]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-97, -99, -102]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1519)) (countLit q [-97, -99, -102]) (countLit q [-104, -106, -107, -108]) (count1518 q) 1 1 (meaning1507 q) (meaning1514 q) (meaning1519 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1514 = false ∨ valuation q 1519 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-97, -99, -102]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-97, -99, -102]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1507)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1520)) (countLit q [-97, -99, -102]) (countLit q [-104, -106, -107, -108]) (count1518 q) 1 2 (meaning1507 q) (meaning1515 q) (meaning1520 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1515 = false ∨ valuation q 1520 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true := by
  have hs : count1518 q = (countLit q [-97, -99, -102]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-97, -99, -102]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1520)) (countLit q [-97, -99, -102]) (countLit q [-104, -106, -107, -108]) (count1518 q) 2 1 (meaning1508 q) (meaning1514 q) (meaning1520 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1514 = false ∨ valuation q 1520 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true := by
  have hs : count1518 q = (countLit q [-97, -99, -102]) + (countLit q [-104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-97, -99, -102]) (l₂ := [-104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1521)) (countLit q [-97, -99, -102]) (countLit q [-104, -106, -107, -108]) (count1518 q) 3 1 (meaning1509 q) (meaning1514 q) (meaning1521 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1514 = false ∨ valuation q 1521 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1526 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1518)) (literal (valuationOf q) (1526)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 1 1 (meaning1498 q) (meaning1518 q) (meaning1526 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1518 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1518 = false ∨ valuation q 1526 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1527 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1527)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 1 2 (meaning1498 q) (meaning1519 q) (meaning1527 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1519 = false ∨ valuation q 1527 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1528 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1528)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 1 3 (meaning1498 q) (meaning1520 q) (meaning1528 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1520 = false ∨ valuation q 1528 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 1498 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1529 = true := by
  have hs : count1525 q = (countLit q [-84, -85, -86, -88, -90, -93, -94]) + (countLit q [-97, -99, -102, -104, -106, -107, -108]) := List.countP_append (p := literal q) (l₁ := [-84, -85, -86, -88, -90, -93, -94]) (l₂ := [-97, -99, -102, -104, -106, -107, -108])
  have hm := merge_two (literal (valuationOf q) (1498)) (literal (valuationOf q) (1521)) (literal (valuationOf q) (1529)) (countLit q [-84, -85, -86, -88, -90, -93, -94]) (countLit q [-97, -99, -102, -104, -106, -107, -108]) (count1525 q) 1 4 (meaning1498 q) (meaning1521 q) (meaning1529 q) hs
  change valuationOf q 1498 = false ∨ valuationOf q 1521 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 1498 = false ∨ valuation q 1521 = false ∨ valuation q 1529 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E107.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112107
