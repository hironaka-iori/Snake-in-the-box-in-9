import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-59]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1526)) (literal (valuationOf q) (1528)) (countLit q [-59]) (countLit q [-62, -63]) (count1528 q) 1 (meaning1526 q) (meaning1528 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1528 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-59]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62, -63])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1529)) (countLit q [-59]) (countLit q [-62, -63]) (count1528 q) 2 (meaning1527 q) (meaning1529 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1529 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1526 = false ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-59]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1529)) (countLit q [-59]) (countLit q [-62, -63]) (count1528 q) 1 1 (meaningNeg59 q) (meaning1526 q) (meaning1529 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1526 = false ∨ valuation q 1529 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true := by
  have hs : count1528 q = (countLit q [-59]) + (countLit q [-62, -63]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62, -63])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1530)) (countLit q [-59]) (countLit q [-62, -63]) (count1528 q) 1 2 (meaningNeg59 q) (meaning1527 q) (meaning1530 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1527 = false ∨ valuation q 1530 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1531)) (countLit q [-64]) (countLit q [-66]) (count1531 q) 1 (meaningNeg66 q) (meaning1531 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1531 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1531 = true := by
  have hs : count1531 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1531)) (countLit q [-64]) (countLit q [-66]) (count1531 q) 1 (meaningNeg64 q) (meaning1531 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1531 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1532 = true := by
  have hs : count1531 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1532)) (countLit q [-64]) (countLit q [-66]) (count1531 q) 1 1 (meaningNeg64 q) (meaningNeg66 q) (meaning1532 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 1532 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1533)) (countLit q [-70]) (countLit q [-71]) (count1533 q) 1 (meaningNeg71 q) (meaning1533 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1533 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1533)) (countLit q [-70]) (countLit q [-71]) (count1533 q) 1 (meaningNeg70 q) (meaning1533 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1533 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-70]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1534)) (countLit q [-70]) (countLit q [-71]) (count1533 q) 1 1 (meaningNeg70 q) (meaningNeg71 q) (meaning1534 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 71 = true ∨ valuation q 1534 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-64, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-70, -71])
  have hm := merge_right (literal (valuationOf q) (1533)) (literal (valuationOf q) (1535)) (countLit q [-64, -66]) (countLit q [-70, -71]) (count1535 q) 1 (meaning1533 q) (meaning1535 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1535 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-64, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-70, -71])
  have hm := merge_right (literal (valuationOf q) (1534)) (literal (valuationOf q) (1536)) (countLit q [-64, -66]) (countLit q [-70, -71]) (count1535 q) 2 (meaning1534 q) (meaning1536 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1536 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-64, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-70, -71])
  have hm := merge_left (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-64, -66]) (countLit q [-70, -71]) (count1535 q) 1 (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1535 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-64, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1536)) (countLit q [-64, -66]) (countLit q [-70, -71]) (count1535 q) 1 1 (meaning1531 q) (meaning1533 q) (meaning1536 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = false ∨ valuation q 1536 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1537 = true := by
  have hs : count1535 q = (countLit q [-64, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1537)) (countLit q [-64, -66]) (countLit q [-70, -71]) (count1535 q) 1 2 (meaning1531 q) (meaning1534 q) (meaning1537 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1534 = false ∨ valuation q 1537 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-64, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-70, -71])
  have hm := merge_left (literal (valuationOf q) (1532)) (literal (valuationOf q) (1536)) (countLit q [-64, -66]) (countLit q [-70, -71]) (count1535 q) 2 (meaning1532 q) (meaning1536 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1536 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1535 q = (countLit q [-64, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-64, -66]) (countLit q [-70, -71]) (count1535 q) 2 1 (meaning1532 q) (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1533 = false ∨ valuation q 1537 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1535 q = (countLit q [-64, -66]) + (countLit q [-70, -71]) := List.countP_append (p := literal q) (l₁ := [-64, -66]) (l₂ := [-70, -71])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-64, -66]) (countLit q [-70, -71]) (count1535 q) 2 2 (meaning1532 q) (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1534 = false ∨ valuation q 1538 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_left (literal (valuationOf q) (1528)) (literal (valuationOf q) (1539)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 1 (meaning1528 q) (meaning1539 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1539 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1540)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 1 1 (meaning1528 q) (meaning1535 q) (meaning1540 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1535 = false ∨ valuation q 1540 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1541)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 1 2 (meaning1528 q) (meaning1536 q) (meaning1541 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1536 = false ∨ valuation q 1541 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_left (literal (valuationOf q) (1529)) (literal (valuationOf q) (1540)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 2 (meaning1529 q) (meaning1540 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1540 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1541)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 2 1 (meaning1529 q) (meaning1535 q) (meaning1541 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1535 = false ∨ valuation q 1541 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1542)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 2 2 (meaning1529 q) (meaning1536 q) (meaning1542 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1536 = false ∨ valuation q 1542 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1543)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 2 3 (meaning1529 q) (meaning1537 q) (meaning1543 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1537 = false ∨ valuation q 1543 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1544)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 2 4 (meaning1529 q) (meaning1538 q) (meaning1544 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1538 = false ∨ valuation q 1544 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_left (literal (valuationOf q) (1530)) (literal (valuationOf q) (1541)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 3 (meaning1530 q) (meaning1541 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1541 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1542)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 3 1 (meaning1530 q) (meaning1535 q) (meaning1542 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1535 = false ∨ valuation q 1542 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1543)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 3 2 (meaning1530 q) (meaning1536 q) (meaning1543 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1536 = false ∨ valuation q 1543 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1544)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 3 3 (meaning1530 q) (meaning1537 q) (meaning1544 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1537 = false ∨ valuation q 1544 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true := by
  have hs : count1539 q = (countLit q [-59, -62, -63]) + (countLit q [-64, -66, -70, -71]) := List.countP_append (p := literal q) (l₁ := [-59, -62, -63]) (l₂ := [-64, -66, -70, -71])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1545)) (countLit q [-59, -62, -63]) (countLit q [-64, -66, -70, -71]) (count1539 q) 3 4 (meaning1530 q) (meaning1538 q) (meaning1545 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1538 = false ∨ valuation q 1545 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-73]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1546)) (countLit q [-73]) (countLit q [-77]) (count1546 q) 1 (meaningNeg77 q) (meaning1546 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1546 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E120.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112120
