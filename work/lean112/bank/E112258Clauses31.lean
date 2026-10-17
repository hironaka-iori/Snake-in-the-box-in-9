import E112258Semantics
import B112E258Inputs
namespace Snake9.Regrowth.E112258
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1539 = true := by
  have hs : count1534 q = (countLit q [-18, -21, -22]) + (countLit q [-25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-18, -21, -22]) (l₂ := [-25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1539)) (countLit q [-18, -21, -22]) (countLit q [-25, -28, -29, -31]) (count1534 q) 3 3 (meaning1525 q) (meaning1532 q) (meaning1539 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1532 = false ∨ valuation q 1539 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1541 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1514)) (literal (valuationOf q) (1541)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 1 (meaning1514 q) (meaning1541 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1541 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1542)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 1 1 (meaning1514 q) (meaning1534 q) (meaning1542 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1534 = false ∨ valuation q 1542 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1543)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 1 2 (meaning1514 q) (meaning1535 q) (meaning1543 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1535 = false ∨ valuation q 1543 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1544)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 1 3 (meaning1514 q) (meaning1536 q) (meaning1544 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1536 = false ∨ valuation q 1544 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1545)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 1 4 (meaning1514 q) (meaning1537 q) (meaning1545 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1537 = false ∨ valuation q 1545 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1546)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 1 5 (meaning1514 q) (meaning1538 q) (meaning1546 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1538 = false ∨ valuation q 1546 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1547)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 1 6 (meaning1514 q) (meaning1539 q) (meaning1547 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1539 = false ∨ valuation q 1547 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1542 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1515)) (literal (valuationOf q) (1542)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 2 (meaning1515 q) (meaning1542 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1542 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1543)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 2 1 (meaning1515 q) (meaning1534 q) (meaning1543 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1534 = false ∨ valuation q 1543 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1544)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 2 2 (meaning1515 q) (meaning1535 q) (meaning1544 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1535 = false ∨ valuation q 1544 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1545)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 2 3 (meaning1515 q) (meaning1536 q) (meaning1545 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1536 = false ∨ valuation q 1545 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1546)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 2 4 (meaning1515 q) (meaning1537 q) (meaning1546 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1537 = false ∨ valuation q 1546 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1547)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 2 5 (meaning1515 q) (meaning1538 q) (meaning1547 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1538 = false ∨ valuation q 1547 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1548)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 2 6 (meaning1515 q) (meaning1539 q) (meaning1548 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1539 = false ∨ valuation q 1548 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1543 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1516)) (literal (valuationOf q) (1543)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 3 (meaning1516 q) (meaning1543 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1543 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1544)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 3 1 (meaning1516 q) (meaning1534 q) (meaning1544 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1534 = false ∨ valuation q 1544 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1545)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 3 2 (meaning1516 q) (meaning1535 q) (meaning1545 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1535 = false ∨ valuation q 1545 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1546)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 3 3 (meaning1516 q) (meaning1536 q) (meaning1546 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1536 = false ∨ valuation q 1546 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1547)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 3 4 (meaning1516 q) (meaning1537 q) (meaning1547 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1537 = false ∨ valuation q 1547 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1548)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 3 5 (meaning1516 q) (meaning1538 q) (meaning1548 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1538 = false ∨ valuation q 1548 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1549)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 3 6 (meaning1516 q) (meaning1539 q) (meaning1549 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1539 = false ∨ valuation q 1549 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1544 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1517)) (literal (valuationOf q) (1544)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 4 (meaning1517 q) (meaning1544 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1544 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1545)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 4 1 (meaning1517 q) (meaning1534 q) (meaning1545 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1534 = false ∨ valuation q 1545 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1546)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 4 2 (meaning1517 q) (meaning1535 q) (meaning1546 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1535 = false ∨ valuation q 1546 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1547)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 4 3 (meaning1517 q) (meaning1536 q) (meaning1547 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1536 = false ∨ valuation q 1547 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1548)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 4 4 (meaning1517 q) (meaning1537 q) (meaning1548 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1537 = false ∨ valuation q 1548 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1549)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 4 5 (meaning1517 q) (meaning1538 q) (meaning1549 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1538 = false ∨ valuation q 1549 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1550)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 4 6 (meaning1517 q) (meaning1539 q) (meaning1550 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1539 = false ∨ valuation q 1550 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1545 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_left (literal (valuationOf q) (1518)) (literal (valuationOf q) (1545)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 5 (meaning1518 q) (meaning1545 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1545 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1546 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1546)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 5 1 (meaning1518 q) (meaning1534 q) (meaning1546 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1534 = false ∨ valuation q 1546 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1547 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -12, -13, -15, -17]) + (countLit q [-18, -21, -22, -25, -28, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -12, -13, -15, -17]) (l₂ := [-18, -21, -22, -25, -28, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1547)) (countLit q [-2, -5, -8, -12, -13, -15, -17]) (countLit q [-18, -21, -22, -25, -28, -29, -31]) (count1541 q) 5 2 (meaning1518 q) (meaning1535 q) (meaning1547 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1535 = false ∨ valuation q 1547 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E258.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112258
