import E112007Semantics
import B112E007Inputs
namespace Snake9.Regrowth.E112007
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1540)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 1 1 (meaning1512 q) (meaning1532 q) (meaning1540 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1532 = false ∨ valuation q 1540 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1541)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 1 2 (meaning1512 q) (meaning1533 q) (meaning1541 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1533 = false ∨ valuation q 1541 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1542)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 1 3 (meaning1512 q) (meaning1534 q) (meaning1542 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1534 = false ∨ valuation q 1542 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1543)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 1 4 (meaning1512 q) (meaning1535 q) (meaning1543 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1535 = false ∨ valuation q 1543 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1544)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 1 5 (meaning1512 q) (meaning1536 q) (meaning1544 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1536 = false ∨ valuation q 1544 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1542)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 2 2 (meaning1513 q) (meaning1533 q) (meaning1542 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1533 = false ∨ valuation q 1542 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1543)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 2 3 (meaning1513 q) (meaning1534 q) (meaning1543 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1534 = false ∨ valuation q 1543 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1544)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 2 4 (meaning1513 q) (meaning1535 q) (meaning1544 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1535 = false ∨ valuation q 1544 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1545 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1545)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 2 5 (meaning1513 q) (meaning1536 q) (meaning1545 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1536 = false ∨ valuation q 1545 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1542)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 3 1 (meaning1514 q) (meaning1532 q) (meaning1542 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1532 = false ∨ valuation q 1542 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1543)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 3 2 (meaning1514 q) (meaning1533 q) (meaning1543 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1533 = false ∨ valuation q 1543 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1544)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 3 3 (meaning1514 q) (meaning1534 q) (meaning1544 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1534 = false ∨ valuation q 1544 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1545)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 3 4 (meaning1514 q) (meaning1535 q) (meaning1545 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1535 = false ∨ valuation q 1545 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1546)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 3 5 (meaning1514 q) (meaning1536 q) (meaning1546 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1536 = false ∨ valuation q 1546 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1544)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 4 2 (meaning1515 q) (meaning1533 q) (meaning1544 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1533 = false ∨ valuation q 1544 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1545 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1545)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 4 3 (meaning1515 q) (meaning1534 q) (meaning1545 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1534 = false ∨ valuation q 1545 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1545 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1545)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 5 2 (meaning1516 q) (meaning1533 q) (meaning1545 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1533 = false ∨ valuation q 1545 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1546 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1546)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -55, -57, -59]) (count1539 q) 6 2 (meaning1517 q) (meaning1533 q) (meaning1546 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1533 = false ∨ valuation q 1546 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_right (literal (valuationOf q) (1545)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 7 (meaning1545 q) (meaning1559 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1559 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1556 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 1 3 (meaning1485 q) (meaning1541 q) (meaning1556 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1541 = false ∨ valuation q 1556 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 1 4 (meaning1485 q) (meaning1542 q) (meaning1557 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1542 = false ∨ valuation q 1557 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 1 5 (meaning1485 q) (meaning1543 q) (meaning1558 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1543 = false ∨ valuation q 1558 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 1 6 (meaning1485 q) (meaning1544 q) (meaning1559 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1544 = false ∨ valuation q 1559 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 1 7 (meaning1485 q) (meaning1545 q) (meaning1560 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1545 = false ∨ valuation q 1560 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 1 8 (meaning1485 q) (meaning1546 q) (meaning1561 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1546 = false ∨ valuation q 1561 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 2 3 (meaning1486 q) (meaning1541 q) (meaning1557 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1541 = false ∨ valuation q 1557 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 2 4 (meaning1486 q) (meaning1542 q) (meaning1558 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1542 = false ∨ valuation q 1558 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 2 5 (meaning1486 q) (meaning1543 q) (meaning1559 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1543 = false ∨ valuation q 1559 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 2 6 (meaning1486 q) (meaning1544 q) (meaning1560 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1544 = false ∨ valuation q 1560 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 2 7 (meaning1486 q) (meaning1545 q) (meaning1561 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1545 = false ∨ valuation q 1561 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 3 3 (meaning1487 q) (meaning1541 q) (meaning1558 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1541 = false ∨ valuation q 1558 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -55, -57, -59]) (count1553 q) 3 4 (meaning1487 q) (meaning1542 q) (meaning1559 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1542 = false ∨ valuation q 1559 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E007.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112007
