import E112152Semantics
import B112E152Inputs
namespace Snake9.Regrowth.E112152
noncomputable section
local instance blockDec20 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause641 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_left (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1535 q) 1 (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause641 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1535 = true := counterClause641 (baseVal q)

theorem counterClause642 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1536)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1535 q) 1 1 (meaning1531 q) (meaning1533 q) (meaning1536 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause642 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = false ∨ valuation q 1536 = true := counterClause642 (baseVal q)

theorem counterClause643 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1537 = true := by
  have hs : count1535 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1537)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1535 q) 1 2 (meaning1531 q) (meaning1534 q) (meaning1537 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause643 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1534 = false ∨ valuation q 1537 = true := counterClause643 (baseVal q)

theorem counterClause644 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_left (literal (valuationOf q) (1532)) (literal (valuationOf q) (1536)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1535 q) 2 (meaning1532 q) (meaning1536 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause644 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1536 = true := counterClause644 (baseVal q)

theorem counterClause645 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1535 q = (countLit q [-46, -47]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-46, -47]) (countLit q [-48, -50]) (count1535 q) 2 1 (meaning1532 q) (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause645 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1533 = false ∨ valuation q 1537 = true := counterClause645 (baseVal q)

theorem counterClause646 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (1539)) (countLit q [-53]) (countLit q [-55]) (count1539 q) 1 (meaningNeg55 q) (meaning1539 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause646 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1539 = true := counterClause646 (baseVal q)

theorem counterClause647 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1539)) (countLit q [-53]) (countLit q [-55]) (count1539 q) 1 (meaningNeg53 q) (meaning1539 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause647 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1539 = true := counterClause647 (baseVal q)

theorem counterClause648 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 55 = true ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-53]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (1540)) (countLit q [-53]) (countLit q [-55]) (count1539 q) 1 1 (meaningNeg53 q) (meaningNeg55 q) (meaning1540 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause648 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 55 = true ∨ valuation q 1540 = true := counterClause648 (baseVal q)

theorem counterClause649 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (1541)) (countLit q [-56]) (countLit q [-59]) (count1541 q) 1 (meaningNeg59 q) (meaning1541 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause649 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1541 = true := counterClause649 (baseVal q)

theorem counterClause650 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1541)) (countLit q [-56]) (countLit q [-59]) (count1541 q) 1 (meaningNeg56 q) (meaning1541 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause650 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1541 = true := counterClause650 (baseVal q)

theorem counterClause651 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 59 = true ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-56]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-59])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-59)) (literal (valuationOf q) (1542)) (countLit q [-56]) (countLit q [-59]) (count1541 q) 1 1 (meaningNeg56 q) (meaningNeg59 q) (meaning1542 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 59)) = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause651 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 59 = true ∨ valuation q 1542 = true := counterClause651 (baseVal q)

theorem counterClause652 (q : Nat → Bool) : valuationOf q 1541 = false ∨ valuationOf q 1543 = true := by
  have hs : count1543 q = (countLit q [-53, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -59])
  have hm := merge_right (literal (valuationOf q) (1541)) (literal (valuationOf q) (1543)) (countLit q [-53, -55]) (countLit q [-56, -59]) (count1543 q) 1 (meaning1541 q) (meaning1543 q) hs
  change valuationOf q 1541 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause652 (q : Snake 81) (h : Conditions q) : valuation q 1541 = false ∨ valuation q 1543 = true := counterClause652 (baseVal q)

theorem counterClause653 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1543 = true := by
  have hs : count1543 q = (countLit q [-53, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -59])
  have hm := merge_left (literal (valuationOf q) (1539)) (literal (valuationOf q) (1543)) (countLit q [-53, -55]) (countLit q [-56, -59]) (count1543 q) 1 (meaning1539 q) (meaning1543 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause653 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1543 = true := counterClause653 (baseVal q)

theorem counterClause654 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1544 = true := by
  have hs : count1543 q = (countLit q [-53, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -59])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1544)) (countLit q [-53, -55]) (countLit q [-56, -59]) (count1543 q) 1 1 (meaning1539 q) (meaning1541 q) (meaning1544 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause654 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1541 = false ∨ valuation q 1544 = true := counterClause654 (baseVal q)

theorem counterClause655 (q : Nat → Bool) : valuationOf q 1539 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1545 = true := by
  have hs : count1543 q = (countLit q [-53, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -59])
  have hm := merge_two (literal (valuationOf q) (1539)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1545)) (countLit q [-53, -55]) (countLit q [-56, -59]) (count1543 q) 1 2 (meaning1539 q) (meaning1542 q) (meaning1545 q) hs
  change valuationOf q 1539 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause655 (q : Snake 81) (h : Conditions q) : valuation q 1539 = false ∨ valuation q 1542 = false ∨ valuation q 1545 = true := counterClause655 (baseVal q)

theorem counterClause656 (q : Nat → Bool) : valuationOf q 1540 = false ∨ valuationOf q 1544 = true := by
  have hs : count1543 q = (countLit q [-53, -55]) + (countLit q [-56, -59]) := List.countP_append (p := literal q) (l₁ := [-53, -55]) (l₂ := [-56, -59])
  have hm := merge_left (literal (valuationOf q) (1540)) (literal (valuationOf q) (1544)) (countLit q [-53, -55]) (countLit q [-56, -59]) (count1543 q) 2 (meaning1540 q) (meaning1544 q) hs
  change valuationOf q 1540 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause656 (q : Snake 81) (h : Conditions q) : valuation q 1540 = false ∨ valuation q 1544 = true := counterClause656 (baseVal q)

theorem counterClause657 (q : Nat → Bool) : valuationOf q 1543 = false ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (1543)) (literal (valuationOf q) (1547)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 1 (meaning1543 q) (meaning1547 q) hs
  change valuationOf q 1543 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause657 (q : Snake 81) (h : Conditions q) : valuation q 1543 = false ∨ valuation q 1547 = true := counterClause657 (baseVal q)

theorem counterClause658 (q : Nat → Bool) : valuationOf q 1544 = false ∨ valuationOf q 1548 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_right (literal (valuationOf q) (1544)) (literal (valuationOf q) (1548)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 2 (meaning1544 q) (meaning1548 q) hs
  change valuationOf q 1544 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause658 (q : Snake 81) (h : Conditions q) : valuation q 1544 = false ∨ valuation q 1548 = true := counterClause658 (baseVal q)

theorem counterClause659 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1547 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (1535)) (literal (valuationOf q) (1547)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 1 (meaning1535 q) (meaning1547 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause659 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1547 = true := counterClause659 (baseVal q)

theorem counterClause660 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1548 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1548)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 1 1 (meaning1535 q) (meaning1543 q) (meaning1548 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause660 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1543 = false ∨ valuation q 1548 = true := counterClause660 (baseVal q)

theorem counterClause661 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1549 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1549)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 1 2 (meaning1535 q) (meaning1544 q) (meaning1549 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause661 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1544 = false ∨ valuation q 1549 = true := counterClause661 (baseVal q)

theorem counterClause662 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1550 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1535)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1550)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 1 3 (meaning1535 q) (meaning1545 q) (meaning1550 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause662 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1545 = false ∨ valuation q 1550 = true := counterClause662 (baseVal q)

theorem counterClause663 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1548 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (1536)) (literal (valuationOf q) (1548)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 2 (meaning1536 q) (meaning1548 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause663 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1548 = true := counterClause663 (baseVal q)

theorem counterClause664 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1549 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1549)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 2 1 (meaning1536 q) (meaning1543 q) (meaning1549 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause664 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1543 = false ∨ valuation q 1549 = true := counterClause664 (baseVal q)

theorem counterClause665 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1550 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1536)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1550)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 2 2 (meaning1536 q) (meaning1544 q) (meaning1550 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause665 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1544 = false ∨ valuation q 1550 = true := counterClause665 (baseVal q)

theorem counterClause666 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1549 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_left (literal (valuationOf q) (1537)) (literal (valuationOf q) (1549)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 3 (meaning1537 q) (meaning1549 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause666 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1549 = true := counterClause666 (baseVal q)

theorem counterClause667 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1550 = true := by
  have hs : count1547 q = (countLit q [-46, -47, -48, -50]) + (countLit q [-53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -47, -48, -50]) (l₂ := [-53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1537)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1550)) (countLit q [-46, -47, -48, -50]) (countLit q [-53, -55, -56, -59]) (count1547 q) 3 1 (meaning1537 q) (meaning1543 q) (meaning1550 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause667 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1543 = false ∨ valuation q 1550 = true := counterClause667 (baseVal q)

theorem counterClause668 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1556)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 1 1 (meaning1524 q) (meaning1547 q) (meaning1556 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause668 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1547 = false ∨ valuation q 1556 = true := counterClause668 (baseVal q)

theorem counterClause669 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1557 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1557)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 1 2 (meaning1524 q) (meaning1548 q) (meaning1557 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause669 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1548 = false ∨ valuation q 1557 = true := counterClause669 (baseVal q)

theorem counterClause670 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1558 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1558)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 1 3 (meaning1524 q) (meaning1549 q) (meaning1558 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause670 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1549 = false ∨ valuation q 1558 = true := counterClause670 (baseVal q)

theorem counterClause671 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1559 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1559)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 1 4 (meaning1524 q) (meaning1550 q) (meaning1559 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause671 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1550 = false ∨ valuation q 1559 = true := counterClause671 (baseVal q)

theorem counterClause672 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true := by
  have hs : count1555 q = (countLit q [-30, -33, -37, -38, -39, -40, -44]) + (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -37, -38, -39, -40, -44]) (l₂ := [-46, -47, -48, -50, -53, -55, -56, -59])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1557)) (countLit q [-30, -33, -37, -38, -39, -40, -44]) (countLit q [-46, -47, -48, -50, -53, -55, -56, -59]) (count1555 q) 2 1 (meaning1525 q) (meaning1547 q) (meaning1557 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause672 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1547 = false ∨ valuation q 1557 = true := counterClause672 (baseVal q)

theorem block20 (q : Snake 81) (h : Conditions q) : B112E152.Block20 (valuation q) :=
  ⟨clause641 q h, clause642 q h, clause643 q h, clause644 q h, clause645 q h, clause646 q h, clause647 q h, clause648 q h, clause649 q h, clause650 q h, clause651 q h, clause652 q h, clause653 q h, clause654 q h, clause655 q h, clause656 q h, clause657 q h, clause658 q h, clause659 q h, clause660 q h, clause661 q h, clause662 q h, clause663 q h, clause664 q h, clause665 q h, clause666 q h, clause667 q h, clause668 q h, clause669 q h, clause670 q h, clause671 q h, clause672 q h⟩

end
end Snake9.Regrowth.E112152
