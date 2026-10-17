import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 4 3 (meaning1389 q) (meaning1408 q) (meaning1419 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1408 = false ∨ valuation q 1419 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1420 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1420)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 4 4 (meaning1389 q) (meaning1409 q) (meaning1420 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1409 = false ∨ valuation q 1420 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1421 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1421)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 4 5 (meaning1389 q) (meaning1410 q) (meaning1421 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1410 = false ∨ valuation q 1421 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1417 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_left (literal (valuationOf q) (1390)) (literal (valuationOf q) (1417)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 5 (meaning1390 q) (meaning1417 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1417 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1418 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1418)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 5 1 (meaning1390 q) (meaning1406 q) (meaning1418 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1406 = false ∨ valuation q 1418 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 5 2 (meaning1390 q) (meaning1407 q) (meaning1419 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1407 = false ∨ valuation q 1419 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1420 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1420)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 5 3 (meaning1390 q) (meaning1408 q) (meaning1420 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1408 = false ∨ valuation q 1420 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1421 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1421)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 5 4 (meaning1390 q) (meaning1409 q) (meaning1421 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1409 = false ∨ valuation q 1421 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1419)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 6 1 (meaning1391 q) (meaning1406 q) (meaning1419 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1406 = false ∨ valuation q 1419 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1420 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1420)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 6 2 (meaning1391 q) (meaning1407 q) (meaning1420 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1407 = false ∨ valuation q 1420 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1421 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1421)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 6 3 (meaning1391 q) (meaning1408 q) (meaning1421 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1408 = false ∨ valuation q 1421 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1422 = true := by
  have hs : count1413 q = (countLit q [-2, -3, -5, -8, -10, -11, -12]) + (countLit q [-15, -17, -18, -21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5, -8, -10, -11, -12]) (l₂ := [-15, -17, -18, -21, -24, -26, -29])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1422)) (countLit q [-2, -3, -5, -8, -10, -11, -12]) (countLit q [-15, -17, -18, -21, -24, -26, -29]) (count1413 q) 6 4 (meaning1391 q) (meaning1409 q) (meaning1422 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1409 = false ∨ valuation q 1422 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1427 = true := by
  have hs : count1427 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (1427)) (countLit q [-31]) (countLit q [-34]) (count1427 q) 1 (meaningNeg34 q) (meaning1427 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1427 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1427 = true := by
  have hs : count1427 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (1427)) (countLit q [-31]) (countLit q [-34]) (count1427 q) 1 (meaningNeg31 q) (meaning1427 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1427 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 34 = true ∨ valuationOf q 1428 = true := by
  have hs : count1427 q = (countLit q [-31]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-31)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (1428)) (countLit q [-31]) (countLit q [-34]) (count1427 q) 1 1 (meaningNeg31 q) (meaningNeg34 q) (meaning1428 q) hs
  change (! (valuationOf q 31)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 34 = true ∨ valuation q 1428 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1429 = true := by
  have hs : count1429 q = (countLit q [-30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -34])
  have hm := merge_right (literal (valuationOf q) (1427)) (literal (valuationOf q) (1429)) (countLit q [-30]) (countLit q [-31, -34]) (count1429 q) 1 (meaning1427 q) (meaning1429 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1429 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1430 = true := by
  have hs : count1429 q = (countLit q [-30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -34])
  have hm := merge_right (literal (valuationOf q) (1428)) (literal (valuationOf q) (1430)) (countLit q [-30]) (countLit q [-31, -34]) (count1429 q) 2 (meaning1428 q) (meaning1430 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1430 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1429 = true := by
  have hs : count1429 q = (countLit q [-30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -34])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (1429)) (countLit q [-30]) (countLit q [-31, -34]) (count1429 q) 1 (meaningNeg30 q) (meaning1429 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1429 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1427 = false ∨ valuationOf q 1430 = true := by
  have hs : count1429 q = (countLit q [-30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -34])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1427)) (literal (valuationOf q) (1430)) (countLit q [-30]) (countLit q [-31, -34]) (count1429 q) 1 1 (meaningNeg30 q) (meaning1427 q) (meaning1430 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1427 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1427 = false ∨ valuation q 1430 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true := by
  have hs : count1429 q = (countLit q [-30]) + (countLit q [-31, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-31, -34])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (1428)) (literal (valuationOf q) (1431)) (countLit q [-30]) (countLit q [-31, -34]) (count1429 q) 1 2 (meaningNeg30 q) (meaning1428 q) (meaning1431 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1428 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1428 = false ∨ valuation q 1431 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1432 = true := by
  have hs : count1432 q = (countLit q [-36]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1432)) (countLit q [-36]) (countLit q [-39]) (count1432 q) 1 (meaningNeg39 q) (meaning1432 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1432 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1432 = true := by
  have hs : count1432 q = (countLit q [-36]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (1432)) (countLit q [-36]) (countLit q [-39]) (count1432 q) 1 (meaningNeg36 q) (meaning1432 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1432 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 39 = true ∨ valuationOf q 1433 = true := by
  have hs : count1432 q = (countLit q [-36]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (1433)) (countLit q [-36]) (countLit q [-39]) (count1432 q) 1 1 (meaningNeg36 q) (meaningNeg39 q) (meaning1433 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 39 = true ∨ valuation q 1433 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-40]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43])
  have hm := merge_right (literal (valuationOf q) (-43)) (literal (valuationOf q) (1434)) (countLit q [-40]) (countLit q [-43]) (count1434 q) 1 (meaningNeg43 q) (meaning1434 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 1434 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-40]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (1434)) (countLit q [-40]) (countLit q [-43]) (count1434 q) 1 (meaningNeg40 q) (meaning1434 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 1434 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 43 = true ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-40]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-43])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-43)) (literal (valuationOf q) (1435)) (countLit q [-40]) (countLit q [-43]) (count1434 q) 1 1 (meaningNeg40 q) (meaningNeg43 q) (meaning1435 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 43)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 43 = true ∨ valuation q 1435 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-36, -39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -43])
  have hm := merge_right (literal (valuationOf q) (1434)) (literal (valuationOf q) (1436)) (countLit q [-36, -39]) (countLit q [-40, -43]) (count1436 q) 1 (meaning1434 q) (meaning1436 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1436 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1437 = true := by
  have hs : count1436 q = (countLit q [-36, -39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -43])
  have hm := merge_right (literal (valuationOf q) (1435)) (literal (valuationOf q) (1437)) (countLit q [-36, -39]) (countLit q [-40, -43]) (count1436 q) 2 (meaning1435 q) (meaning1437 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1437 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1436 = true := by
  have hs : count1436 q = (countLit q [-36, -39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -43])
  have hm := merge_left (literal (valuationOf q) (1432)) (literal (valuationOf q) (1436)) (countLit q [-36, -39]) (countLit q [-40, -43]) (count1436 q) 1 (meaning1432 q) (meaning1436 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1436 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1437 = true := by
  have hs : count1436 q = (countLit q [-36, -39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -43])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1434)) (literal (valuationOf q) (1437)) (countLit q [-36, -39]) (countLit q [-40, -43]) (count1436 q) 1 1 (meaning1432 q) (meaning1434 q) (meaning1437 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1434 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1434 = false ∨ valuation q 1437 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1438 = true := by
  have hs : count1436 q = (countLit q [-36, -39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -43])
  have hm := merge_two (literal (valuationOf q) (1432)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1438)) (countLit q [-36, -39]) (countLit q [-40, -43]) (count1436 q) 1 2 (meaning1432 q) (meaning1435 q) (meaning1438 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1435 = false ∨ valuation q 1438 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1437 = true := by
  have hs : count1436 q = (countLit q [-36, -39]) + (countLit q [-40, -43]) := List.countP_append (p := literal q) (l₁ := [-36, -39]) (l₂ := [-40, -43])
  have hm := merge_left (literal (valuationOf q) (1433)) (literal (valuationOf q) (1437)) (countLit q [-36, -39]) (countLit q [-40, -43]) (count1436 q) 2 (meaning1433 q) (meaning1437 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1437 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E168.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112168
