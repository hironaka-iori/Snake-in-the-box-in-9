import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true := by
  have hs : count1426 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1416)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1429)) (countLit q [-3, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1426 q) 2 2 (meaning1416 q) (meaning1423 q) (meaning1429 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1423 = false ∨ valuation q 1429 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1428 = true := by
  have hs : count1426 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1417)) (literal (valuationOf q) (1428)) (countLit q [-3, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1426 q) 3 (meaning1417 q) (meaning1428 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1428 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1429 = true := by
  have hs : count1426 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1429)) (countLit q [-3, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1426 q) 3 1 (meaning1417 q) (meaning1422 q) (meaning1429 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1422 = false ∨ valuation q 1429 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1430 = true := by
  have hs : count1426 q = (countLit q [-3, -4, -6]) + (countLit q [-8, -10, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-8, -10, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1430)) (countLit q [-3, -4, -6]) (countLit q [-8, -10, -12, -13]) (count1426 q) 3 2 (meaning1417 q) (meaning1423 q) (meaning1430 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1423 = false ∨ valuation q 1430 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1433)) (countLit q [-15]) (countLit q [-18]) (count1433 q) 1 (meaningNeg18 q) (meaning1433 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1433 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-15]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1433)) (countLit q [-15]) (countLit q [-18]) (count1433 q) 1 (meaningNeg15 q) (meaning1433 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1433 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1435)) (countLit q [-19]) (countLit q [-21]) (count1435 q) 1 (meaningNeg21 q) (meaning1435 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1435 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1435)) (countLit q [-19]) (countLit q [-21]) (count1435 q) 1 (meaningNeg19 q) (meaning1435 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1435 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-19]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1436)) (countLit q [-19]) (countLit q [-21]) (count1435 q) 1 1 (meaningNeg19 q) (meaningNeg21 q) (meaning1436 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 21 = true ∨ valuation q 1436 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (1435)) (literal (valuationOf q) (1437)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1437 q) 1 (meaning1435 q) (meaning1437 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1437 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1436 = false ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_right (literal (valuationOf q) (1436)) (literal (valuationOf q) (1438)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1437 q) 2 (meaning1436 q) (meaning1438 q) hs
  change valuationOf q 1436 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1436 = false ∨ valuation q 1438 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1437 = true := by
  have hs : count1437 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_left (literal (valuationOf q) (1433)) (literal (valuationOf q) (1437)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1437 q) 1 (meaning1433 q) (meaning1437 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1437 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1438 = true := by
  have hs : count1437 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1435)) (literal (valuationOf q) (1438)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1437 q) 1 1 (meaning1433 q) (meaning1435 q) (meaning1438 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1435 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1435 = false ∨ valuation q 1438 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true := by
  have hs : count1437 q = (countLit q [-15, -18]) + (countLit q [-19, -21]) := List.countP_append (p := literal q) (l₁ := [-15, -18]) (l₂ := [-19, -21])
  have hm := merge_two (literal (valuationOf q) (1433)) (literal (valuationOf q) (1436)) (literal (valuationOf q) (1439)) (countLit q [-15, -18]) (countLit q [-19, -21]) (count1437 q) 1 2 (meaning1433 q) (meaning1436 q) (meaning1439 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1436 = false ∨ valuationOf q 1439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1436 = false ∨ valuation q 1439 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1441)) (countLit q [-24]) (countLit q [-26]) (count1441 q) 1 (meaningNeg26 q) (meaning1441 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1441 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1441)) (countLit q [-24]) (countLit q [-26]) (count1441 q) 1 (meaningNeg24 q) (meaning1441 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1441 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1442)) (countLit q [-24]) (countLit q [-26]) (count1441 q) 1 1 (meaningNeg24 q) (meaningNeg26 q) (meaning1442 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 1442 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1443)) (countLit q [-28]) (countLit q [-29]) (count1443 q) 1 (meaningNeg29 q) (meaning1443 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1443 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1443)) (countLit q [-28]) (countLit q [-29]) (count1443 q) 1 (meaningNeg28 q) (meaning1443 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1443 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-24, -26]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -29])
  have hm := merge_right (literal (valuationOf q) (1443)) (literal (valuationOf q) (1445)) (countLit q [-24, -26]) (countLit q [-28, -29]) (count1445 q) 1 (meaning1443 q) (meaning1445 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1445 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1445 = true := by
  have hs : count1445 q = (countLit q [-24, -26]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -29])
  have hm := merge_left (literal (valuationOf q) (1441)) (literal (valuationOf q) (1445)) (countLit q [-24, -26]) (countLit q [-28, -29]) (count1445 q) 1 (meaning1441 q) (meaning1445 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1445 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-24, -26]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -29])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1446)) (countLit q [-24, -26]) (countLit q [-28, -29]) (count1445 q) 1 1 (meaning1441 q) (meaning1443 q) (meaning1446 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = false ∨ valuation q 1446 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1446 = true := by
  have hs : count1445 q = (countLit q [-24, -26]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -29])
  have hm := merge_left (literal (valuationOf q) (1442)) (literal (valuationOf q) (1446)) (countLit q [-24, -26]) (countLit q [-28, -29]) (count1445 q) 2 (meaning1442 q) (meaning1446 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1446 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1447 = true := by
  have hs : count1445 q = (countLit q [-24, -26]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -29])
  have hm := merge_two (literal (valuationOf q) (1442)) (literal (valuationOf q) (1443)) (literal (valuationOf q) (1447)) (countLit q [-24, -26]) (countLit q [-28, -29]) (count1445 q) 2 1 (meaning1442 q) (meaning1443 q) (meaning1447 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1443 = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1443 = false ∨ valuation q 1447 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1449 = true := by
  have hs : count1449 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-24, -26, -28, -29])
  have hm := merge_right (literal (valuationOf q) (1445)) (literal (valuationOf q) (1449)) (countLit q [-15, -18, -19, -21]) (countLit q [-24, -26, -28, -29]) (count1449 q) 1 (meaning1445 q) (meaning1449 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1449 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-24, -26, -28, -29])
  have hm := merge_right (literal (valuationOf q) (1446)) (literal (valuationOf q) (1450)) (countLit q [-15, -18, -19, -21]) (countLit q [-24, -26, -28, -29]) (count1449 q) 2 (meaning1446 q) (meaning1450 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1450 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1450 = true := by
  have hs : count1449 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1450)) (countLit q [-15, -18, -19, -21]) (countLit q [-24, -26, -28, -29]) (count1449 q) 1 1 (meaning1437 q) (meaning1445 q) (meaning1450 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1445 = false ∨ valuation q 1450 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1451)) (countLit q [-15, -18, -19, -21]) (countLit q [-24, -26, -28, -29]) (count1449 q) 1 2 (meaning1437 q) (meaning1446 q) (meaning1451 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1446 = false ∨ valuation q 1451 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1437 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1437)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1452)) (countLit q [-15, -18, -19, -21]) (countLit q [-24, -26, -28, -29]) (count1449 q) 1 3 (meaning1437 q) (meaning1447 q) (meaning1452 q) hs
  change valuationOf q 1437 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1437 = false ∨ valuation q 1447 = false ∨ valuation q 1452 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1451 = true := by
  have hs : count1449 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1451)) (countLit q [-15, -18, -19, -21]) (countLit q [-24, -26, -28, -29]) (count1449 q) 2 1 (meaning1438 q) (meaning1445 q) (meaning1451 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1445 = false ∨ valuation q 1451 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1438 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1438)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1452)) (countLit q [-15, -18, -19, -21]) (countLit q [-24, -26, -28, -29]) (count1449 q) 2 2 (meaning1438 q) (meaning1446 q) (meaning1452 q) hs
  change valuationOf q 1438 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1438 = false ∨ valuation q 1446 = false ∨ valuation q 1452 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 1439 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1452 = true := by
  have hs : count1449 q = (countLit q [-15, -18, -19, -21]) + (countLit q [-24, -26, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -18, -19, -21]) (l₂ := [-24, -26, -28, -29])
  have hm := merge_two (literal (valuationOf q) (1439)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1452)) (countLit q [-15, -18, -19, -21]) (countLit q [-24, -26, -28, -29]) (count1449 q) 3 1 (meaning1439 q) (meaning1445 q) (meaning1452 q) hs
  change valuationOf q 1439 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 1439 = false ∨ valuation q 1445 = false ∨ valuation q 1452 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E096.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112096
