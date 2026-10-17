import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-66, -67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-70, -72])
  have hm := merge_right (literal (valuationOf q) (1534)) (literal (valuationOf q) (1536)) (countLit q [-66, -67]) (countLit q [-70, -72]) (count1535 q) 2 (meaning1534 q) (meaning1536 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1536 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1535 q = (countLit q [-66, -67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-70, -72])
  have hm := merge_left (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-66, -67]) (countLit q [-70, -72]) (count1535 q) 1 (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1535 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-66, -67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1536)) (countLit q [-66, -67]) (countLit q [-70, -72]) (count1535 q) 1 1 (meaning1531 q) (meaning1533 q) (meaning1536 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = false ∨ valuation q 1536 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1537 = true := by
  have hs : count1535 q = (countLit q [-66, -67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1537)) (countLit q [-66, -67]) (countLit q [-70, -72]) (count1535 q) 1 2 (meaning1531 q) (meaning1534 q) (meaning1537 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1534 = false ∨ valuation q 1537 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-66, -67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-70, -72])
  have hm := merge_left (literal (valuationOf q) (1532)) (literal (valuationOf q) (1536)) (countLit q [-66, -67]) (countLit q [-70, -72]) (count1535 q) 2 (meaning1532 q) (meaning1536 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1536 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1535 q = (countLit q [-66, -67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-66, -67]) (countLit q [-70, -72]) (count1535 q) 2 1 (meaning1532 q) (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1533 = false ∨ valuation q 1537 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1535 q = (countLit q [-66, -67]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-66, -67]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1532)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-66, -67]) (countLit q [-70, -72]) (count1535 q) 2 2 (meaning1532 q) (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1534 = false ∨ valuation q 1538 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 1 (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1539 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1536)) (literal (valuationOf q) (1540)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 2 (meaning1536 q) (meaning1540 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1540 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 1537 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1537)) (literal (valuationOf q) (1541)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 3 (meaning1537 q) (meaning1541 q) hs
  change valuationOf q 1537 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 1537 = false ∨ valuation q 1541 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 1538 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1538)) (literal (valuationOf q) (1542)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 4 (meaning1538 q) (meaning1542 q) hs
  change valuationOf q 1538 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 1538 = false ∨ valuation q 1542 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1528)) (literal (valuationOf q) (1539)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 1 (meaning1528 q) (meaning1539 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1539 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1540)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 1 1 (meaning1528 q) (meaning1535 q) (meaning1540 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1535 = false ∨ valuation q 1540 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1541)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 1 2 (meaning1528 q) (meaning1536 q) (meaning1541 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1536 = false ∨ valuation q 1541 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1542)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 1 3 (meaning1528 q) (meaning1537 q) (meaning1542 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1537 = false ∨ valuation q 1542 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1543)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 1 4 (meaning1528 q) (meaning1538 q) (meaning1543 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1538 = false ∨ valuation q 1543 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1541)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 2 1 (meaning1529 q) (meaning1535 q) (meaning1541 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1535 = false ∨ valuation q 1541 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1542)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 2 2 (meaning1529 q) (meaning1536 q) (meaning1542 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1536 = false ∨ valuation q 1542 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1543)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 2 3 (meaning1529 q) (meaning1537 q) (meaning1543 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1537 = false ∨ valuation q 1543 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1544)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 2 4 (meaning1529 q) (meaning1538 q) (meaning1544 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1538 = false ∨ valuation q 1544 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1542)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 3 1 (meaning1530 q) (meaning1535 q) (meaning1542 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1535 = false ∨ valuation q 1542 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-58, -59, -62]) + (countLit q [-66, -67, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -59, -62]) (l₂ := [-66, -67, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1544)) (countLit q [-58, -59, -62]) (countLit q [-66, -67, -70, -72]) (count1539 q) 3 3 (meaning1530 q) (meaning1537 q) (meaning1544 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1537 = false ∨ valuation q 1544 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1546)) (countLit q [-75]) (countLit q [-77]) (count1546 q) 1 (meaningNeg77 q) (meaning1546 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1546 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1546)) (countLit q [-75]) (countLit q [-77]) (count1546 q) 1 (meaningNeg75 q) (meaning1546 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1546 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1547 = true := by
  have hs : count1546 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1547)) (countLit q [-75]) (countLit q [-77]) (count1546 q) 1 1 (meaningNeg75 q) (meaningNeg77 q) (meaning1547 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 1547 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -77])
  have hm := merge_right (literal (valuationOf q) (1546)) (literal (valuationOf q) (1548)) (countLit q [-74]) (countLit q [-75, -77]) (count1548 q) 1 (meaning1546 q) (meaning1548 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1548 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1549 = true := by
  have hs : count1548 q = (countLit q [-74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -77])
  have hm := merge_right (literal (valuationOf q) (1547)) (literal (valuationOf q) (1549)) (countLit q [-74]) (countLit q [-75, -77]) (count1548 q) 2 (meaning1547 q) (meaning1549 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1549 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -77])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1548)) (countLit q [-74]) (countLit q [-75, -77]) (count1548 q) 1 (meaningNeg74 q) (meaning1548 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1548 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1546 = false ∨ valuationOf q 1549 = true := by
  have hs : count1548 q = (countLit q [-74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -77])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1549)) (countLit q [-74]) (countLit q [-75, -77]) (count1548 q) 1 1 (meaningNeg74 q) (meaning1546 q) (meaning1549 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1546 = false ∨ valuation q 1549 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1547 = false ∨ valuationOf q 1550 = true := by
  have hs : count1548 q = (countLit q [-74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-75, -77])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1550)) (countLit q [-74]) (countLit q [-75, -77]) (count1548 q) 1 2 (meaningNeg74 q) (meaning1547 q) (meaning1550 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1547 = false ∨ valuation q 1550 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-79]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1551)) (countLit q [-79]) (countLit q [-82]) (count1551 q) 1 (meaningNeg82 q) (meaning1551 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1551 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-79]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1551)) (countLit q [-79]) (countLit q [-82]) (count1551 q) 1 (meaningNeg79 q) (meaning1551 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1551 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E058.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112058
