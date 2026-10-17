import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1570 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1570)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 7 4 (meaning1493 q) (meaning1548 q) (meaning1570 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1548 = false ∨ valuation q 1570 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1571 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1571)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 7 5 (meaning1493 q) (meaning1549 q) (meaning1571 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1549 = false ∨ valuation q 1571 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1572 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1572)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 7 6 (meaning1493 q) (meaning1550 q) (meaning1572 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1550 = false ∨ valuation q 1572 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 1493 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1573 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1493)) (literal (valuationOf q) (1551)) (literal (valuationOf q) (1573)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 7 7 (meaning1493 q) (meaning1551 q) (meaning1573 q) hs
  change valuationOf q 1493 = false ∨ valuationOf q 1551 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 1493 = false ∨ valuation q 1551 = false ∨ valuation q 1573 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1571 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1571)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 8 4 (meaning1494 q) (meaning1548 q) (meaning1571 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1548 = false ∨ valuation q 1571 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1572 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1572)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 8 5 (meaning1494 q) (meaning1549 q) (meaning1572 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1549 = false ∨ valuation q 1572 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 1494 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1573 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1494)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1573)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 8 6 (meaning1494 q) (meaning1550 q) (meaning1573 q) hs
  change valuationOf q 1494 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 1494 = false ∨ valuation q 1550 = false ∨ valuation q 1573 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1571 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1571)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 9 3 (meaning1495 q) (meaning1547 q) (meaning1571 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1547 = false ∨ valuation q 1571 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1572 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1572)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 9 4 (meaning1495 q) (meaning1548 q) (meaning1572 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1548 = false ∨ valuation q 1572 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 1495 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1573 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) + (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (l₂ := [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57])
  have hm := merge_two (literal (valuationOf q) (1495)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1573)) (countLit q [-2, -4, -5, -6, -7, -8, -11, -13, -14, -17, -20, -22, -25, -26]) (countLit q [-27, -30, -32, -35, -38, -39, -42, -46, -47, -49, -52, -53, -55, -56, -57]) (count1560 q) 9 5 (meaning1495 q) (meaning1549 q) (meaning1573 q) hs
  change valuationOf q 1495 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 1495 = false ∨ valuation q 1549 = false ∨ valuation q 1573 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1578)) (countLit q [-63]) (countLit q [-66]) (count1578 q) 1 (meaningNeg66 q) (meaning1578 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1578 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1578)) (countLit q [-63]) (countLit q [-66]) (count1578 q) 1 (meaningNeg63 q) (meaning1578 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1578 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1579)) (countLit q [-63]) (countLit q [-66]) (count1578 q) 1 1 (meaningNeg63 q) (meaningNeg66 q) (meaning1579 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 66 = true ∨ valuation q 1579 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (countLit q [-61]) (countLit q [-63, -66]) (count1580 q) 1 (meaning1578 q) (meaning1580 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1579)) (literal (valuationOf q) (1581)) (countLit q [-61]) (countLit q [-63, -66]) (count1580 q) 2 (meaning1579 q) (meaning1581 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1581 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63, -66])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (1580)) (countLit q [-61]) (countLit q [-63, -66]) (count1580 q) 1 (meaningNeg61 q) (meaning1580 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1580 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1581)) (countLit q [-61]) (countLit q [-63, -66]) (count1580 q) 1 1 (meaningNeg61 q) (meaning1578 q) (meaning1581 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1578 = false ∨ valuation q 1581 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-67]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1583)) (countLit q [-67]) (countLit q [-70]) (count1583 q) 1 (meaningNeg70 q) (meaning1583 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1583 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1585)) (countLit q [-72]) (countLit q [-73]) (count1585 q) 1 (meaningNeg73 q) (meaning1585 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1585 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1585)) (countLit q [-72]) (countLit q [-73]) (count1585 q) 1 (meaningNeg72 q) (meaning1585 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1585 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-72]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1586)) (countLit q [-72]) (countLit q [-73]) (count1585 q) 1 1 (meaningNeg72 q) (meaningNeg73 q) (meaning1586 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 73 = true ∨ valuation q 1586 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-67, -70]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (1585)) (literal (valuationOf q) (1587)) (countLit q [-67, -70]) (countLit q [-72, -73]) (count1587 q) 1 (meaning1585 q) (meaning1587 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1587 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-67, -70]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-72, -73])
  have hm := merge_right (literal (valuationOf q) (1586)) (literal (valuationOf q) (1588)) (countLit q [-67, -70]) (countLit q [-72, -73]) (count1587 q) 2 (meaning1586 q) (meaning1588 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1588 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-67, -70]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-72, -73])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-67, -70]) (countLit q [-72, -73]) (count1587 q) 1 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-67, -70]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1588)) (countLit q [-67, -70]) (countLit q [-72, -73]) (count1587 q) 1 1 (meaning1583 q) (meaning1585 q) (meaning1588 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = false ∨ valuation q 1588 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-67, -70]) + (countLit q [-72, -73]) := List.countP_append (p := literal q) (l₁ := [-67, -70]) (l₂ := [-72, -73])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1589)) (countLit q [-67, -70]) (countLit q [-72, -73]) (count1587 q) 1 2 (meaning1583 q) (meaning1586 q) (meaning1589 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1586 = false ∨ valuation q 1589 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -72, -73]) (count1591 q) 1 (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1591 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -72, -73]) (count1591 q) 2 (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1592 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -72, -73])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -72, -73]) (count1591 q) 3 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1591)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -72, -73]) (count1591 q) 1 (meaning1580 q) (meaning1591 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1591 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1592)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -72, -73]) (count1591 q) 1 1 (meaning1580 q) (meaning1587 q) (meaning1592 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1587 = false ∨ valuation q 1592 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -72, -73])
  have hm := merge_left (literal (valuationOf q) (1581)) (literal (valuationOf q) (1592)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -72, -73]) (count1591 q) 2 (meaning1581 q) (meaning1592 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1592 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E078.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112078
