import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1566 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1566)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 2 5 (meaning1488 q) (meaning1549 q) (meaning1566 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1549 = false ∨ valuation q 1566 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1567 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1550)) (literal (valuationOf q) (1567)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 2 6 (meaning1488 q) (meaning1550 q) (meaning1567 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1550 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1550 = false ∨ valuation q 1567 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1564 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1564)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 3 2 (meaning1489 q) (meaning1546 q) (meaning1564 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1546 = false ∨ valuation q 1564 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1565 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1565)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 3 3 (meaning1489 q) (meaning1547 q) (meaning1565 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1547 = false ∨ valuation q 1565 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1566 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1566)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 3 4 (meaning1489 q) (meaning1548 q) (meaning1566 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1548 = false ∨ valuation q 1566 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1567 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1549)) (literal (valuationOf q) (1567)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 3 5 (meaning1489 q) (meaning1549 q) (meaning1567 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1549 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1549 = false ∨ valuation q 1567 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1565 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1565)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 4 2 (meaning1490 q) (meaning1546 q) (meaning1565 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1546 = false ∨ valuation q 1565 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1566 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1566)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 4 3 (meaning1490 q) (meaning1547 q) (meaning1566 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1547 = false ∨ valuation q 1566 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1567 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1567)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 4 4 (meaning1490 q) (meaning1548 q) (meaning1567 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1548 = false ∨ valuation q 1567 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1567 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1567)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 5 3 (meaning1491 q) (meaning1547 q) (meaning1567 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1547 = false ∨ valuation q 1567 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1567 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1567)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 6 2 (meaning1492 q) (meaning1546 q) (meaning1567 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1567 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1546 = false ∨ valuation q 1567 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1578)) (countLit q [-65]) (countLit q [-66]) (count1578 q) 1 (meaningNeg66 q) (meaning1578 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1578 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1578)) (countLit q [-65]) (countLit q [-66]) (count1578 q) 1 (meaningNeg65 q) (meaning1578 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1578 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-65]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1579)) (countLit q [-65]) (countLit q [-66]) (count1578 q) 1 1 (meaningNeg65 q) (meaningNeg66 q) (meaning1579 q) hs
  change (! (valuationOf q 65)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 66 = true ∨ valuation q 1579 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-60]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-65, -66])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (countLit q [-60]) (countLit q [-65, -66]) (count1580 q) 1 (meaning1578 q) (meaning1580 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-60]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-65, -66])
  have hm := merge_right (literal (valuationOf q) (1579)) (literal (valuationOf q) (1581)) (countLit q [-60]) (countLit q [-65, -66]) (count1580 q) 2 (meaning1579 q) (meaning1581 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1581 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1580 = true := by
  have hs : count1580 q = (countLit q [-60]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-65, -66])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1580)) (countLit q [-60]) (countLit q [-65, -66]) (count1580 q) 1 (meaningNeg60 q) (meaning1580 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1580 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true := by
  have hs : count1580 q = (countLit q [-60]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-65, -66])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1578)) (literal (valuationOf q) (1581)) (countLit q [-60]) (countLit q [-65, -66]) (count1580 q) 1 1 (meaningNeg60 q) (meaning1578 q) (meaning1581 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1578 = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1578 = false ∨ valuation q 1581 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1579 = false ∨ valuationOf q 1582 = true := by
  have hs : count1580 q = (countLit q [-60]) + (countLit q [-65, -66]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-65, -66])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1579)) (literal (valuationOf q) (1582)) (countLit q [-60]) (countLit q [-65, -66]) (count1580 q) 1 2 (meaningNeg60 q) (meaning1579 q) (meaning1582 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1579 = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1579 = false ∨ valuation q 1582 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_right (literal (valuationOf q) (-69)) (literal (valuationOf q) (1583)) (countLit q [-68]) (countLit q [-69]) (count1583 q) 1 (meaningNeg69 q) (meaning1583 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1583 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_left (literal (valuationOf q) (-68)) (literal (valuationOf q) (1583)) (countLit q [-68]) (countLit q [-69]) (count1583 q) 1 (meaningNeg68 q) (meaning1583 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 1583 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 69 = true ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-68]) + (countLit q [-69]) := List.countP_append (p := literal q) (l₁ := [-68]) (l₂ := [-69])
  have hm := merge_two (literal (valuationOf q) (-68)) (literal (valuationOf q) (-69)) (literal (valuationOf q) (1584)) (countLit q [-68]) (countLit q [-69]) (count1583 q) 1 1 (meaningNeg68 q) (meaningNeg69 q) (meaning1584 q) hs
  change (! (valuationOf q 68)) = false ∨ (! (valuationOf q 69)) = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 69 = true ∨ valuation q 1584 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (1585)) (countLit q [-70]) (countLit q [-72]) (count1585 q) 1 (meaningNeg72 q) (meaning1585 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1585 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1585)) (countLit q [-70]) (countLit q [-72]) (count1585 q) 1 (meaningNeg70 q) (meaning1585 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1585 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1586)) (countLit q [-70]) (countLit q [-72]) (count1585 q) 1 1 (meaningNeg70 q) (meaningNeg72 q) (meaning1586 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 72 = true ∨ valuation q 1586 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-68, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-68, -69]) (l₂ := [-70, -72])
  have hm := merge_right (literal (valuationOf q) (1585)) (literal (valuationOf q) (1587)) (countLit q [-68, -69]) (countLit q [-70, -72]) (count1587 q) 1 (meaning1585 q) (meaning1587 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1587 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-68, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-68, -69]) (l₂ := [-70, -72])
  have hm := merge_right (literal (valuationOf q) (1586)) (literal (valuationOf q) (1588)) (countLit q [-68, -69]) (countLit q [-70, -72]) (count1587 q) 2 (meaning1586 q) (meaning1588 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1588 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-68, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-68, -69]) (l₂ := [-70, -72])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-68, -69]) (countLit q [-70, -72]) (count1587 q) 1 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-68, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-68, -69]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1588)) (countLit q [-68, -69]) (countLit q [-70, -72]) (count1587 q) 1 1 (meaning1583 q) (meaning1585 q) (meaning1588 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = false ∨ valuation q 1588 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-68, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-68, -69]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1589)) (countLit q [-68, -69]) (countLit q [-70, -72]) (count1587 q) 1 2 (meaning1583 q) (meaning1586 q) (meaning1589 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1586 = false ∨ valuation q 1589 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-68, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-68, -69]) (l₂ := [-70, -72])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1588)) (countLit q [-68, -69]) (countLit q [-70, -72]) (count1587 q) 2 (meaning1584 q) (meaning1588 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1588 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-68, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-68, -69]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-68, -69]) (countLit q [-70, -72]) (count1587 q) 2 1 (meaning1584 q) (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1585 = false ∨ valuation q 1589 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E187.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112187
