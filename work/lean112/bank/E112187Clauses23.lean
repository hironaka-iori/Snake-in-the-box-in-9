import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-52, -56]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -56]) (l₂ := [-58, -59])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (countLit q [-52, -56]) (countLit q [-58, -59]) (count1533 q) 1 (meaning1531 q) (meaning1533 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1533 q = (countLit q [-52, -56]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -56]) (l₂ := [-58, -59])
  have hm := merge_left (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-52, -56]) (countLit q [-58, -59]) (count1533 q) 1 (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1533 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-52, -56]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -56]) (l₂ := [-58, -59])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1534)) (countLit q [-52, -56]) (countLit q [-58, -59]) (count1533 q) 1 1 (meaning1529 q) (meaning1531 q) (meaning1534 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1531 = false ∨ valuation q 1534 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1533 q = (countLit q [-52, -56]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -56]) (l₂ := [-58, -59])
  have hm := merge_left (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-52, -56]) (countLit q [-58, -59]) (count1533 q) 2 (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1534 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true := by
  have hs : count1533 q = (countLit q [-52, -56]) + (countLit q [-58, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -56]) (l₂ := [-58, -59])
  have hm := merge_two (literal (valuationOf q) (1530)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1535)) (countLit q [-52, -56]) (countLit q [-58, -59]) (count1533 q) 2 1 (meaning1530 q) (meaning1531 q) (meaning1535 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1531 = false ∨ valuation q 1535 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 1533 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_right (literal (valuationOf q) (1533)) (literal (valuationOf q) (1537)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 1 (meaning1533 q) (meaning1537 q) hs
  change valuationOf q 1533 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 1533 = false ∨ valuation q 1537 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_right (literal (valuationOf q) (1534)) (literal (valuationOf q) (1538)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 2 (meaning1534 q) (meaning1538 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1538 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_right (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 3 (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1539 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_left (literal (valuationOf q) (1525)) (literal (valuationOf q) (1537)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 1 (meaning1525 q) (meaning1537 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1537 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1538)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 1 1 (meaning1525 q) (meaning1533 q) (meaning1538 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1533 = false ∨ valuation q 1538 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1539)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 1 2 (meaning1525 q) (meaning1534 q) (meaning1539 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1534 = false ∨ valuation q 1539 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_left (literal (valuationOf q) (1526)) (literal (valuationOf q) (1538)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 2 (meaning1526 q) (meaning1538 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1538 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1539)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 2 1 (meaning1526 q) (meaning1533 q) (meaning1539 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1533 = false ∨ valuation q 1539 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1526)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1540)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 2 2 (meaning1526 q) (meaning1534 q) (meaning1540 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1534 = false ∨ valuation q 1540 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_left (literal (valuationOf q) (1527)) (literal (valuationOf q) (1539)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 3 (meaning1527 q) (meaning1539 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1539 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-46, -48, -49, -51]) + (countLit q [-52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -51]) (l₂ := [-52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1527)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1540)) (countLit q [-46, -48, -49, -51]) (countLit q [-52, -56, -58, -59]) (count1537 q) 3 1 (meaning1527 q) (meaning1533 q) (meaning1540 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1533 = false ∨ valuation q 1540 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1546 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1546)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 1 1 (meaning1514 q) (meaning1537 q) (meaning1546 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1537 = false ∨ valuation q 1546 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1547 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1547)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 1 2 (meaning1514 q) (meaning1538 q) (meaning1547 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1538 = false ∨ valuation q 1547 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1548)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 1 3 (meaning1514 q) (meaning1539 q) (meaning1548 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1539 = false ∨ valuation q 1548 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1549)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 1 4 (meaning1514 q) (meaning1540 q) (meaning1549 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1540 = false ∨ valuation q 1549 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1547 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1547)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 2 1 (meaning1515 q) (meaning1537 q) (meaning1547 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1537 = false ∨ valuation q 1547 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1548)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 2 2 (meaning1515 q) (meaning1538 q) (meaning1548 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1538 = false ∨ valuation q 1548 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1549)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 2 3 (meaning1515 q) (meaning1539 q) (meaning1549 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1539 = false ∨ valuation q 1549 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1550)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 2 4 (meaning1515 q) (meaning1540 q) (meaning1550 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1540 = false ∨ valuation q 1550 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1548)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 3 1 (meaning1516 q) (meaning1537 q) (meaning1548 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1537 = false ∨ valuation q 1548 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1549)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 3 2 (meaning1516 q) (meaning1538 q) (meaning1549 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1538 = false ∨ valuation q 1549 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1516)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1550)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 3 3 (meaning1516 q) (meaning1539 q) (meaning1550 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1539 = false ∨ valuation q 1550 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1549)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 4 1 (meaning1517 q) (meaning1537 q) (meaning1549 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1537 = false ∨ valuation q 1549 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1517)) (literal (valuationOf q) (1538)) (literal (valuationOf q) (1550)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 4 2 (meaning1517 q) (meaning1538 q) (meaning1550 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1538 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1538 = false ∨ valuation q 1550 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1550 = true := by
  have hs : count1545 q = (countLit q [-32, -34, -35, -39, -40, -41, -42]) + (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -40, -41, -42]) (l₂ := [-46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1518)) (literal (valuationOf q) (1537)) (literal (valuationOf q) (1550)) (countLit q [-32, -34, -35, -39, -40, -41, -42]) (countLit q [-46, -48, -49, -51, -52, -56, -58, -59]) (count1545 q) 5 1 (meaning1518 q) (meaning1537 q) (meaning1550 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1537 = false ∨ valuationOf q 1550 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1537 = false ∨ valuation q 1550 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1564 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1547)) (literal (valuationOf q) (1564)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 2 3 (meaning1488 q) (meaning1547 q) (meaning1564 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1547 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1547 = false ∨ valuation q 1564 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1565 = true := by
  have hs : count1560 q = (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) + (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (l₂ := [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1548)) (literal (valuationOf q) (1565)) (countLit q [-2, -4, -6, -10, -11, -12, -13, -17, -21, -23, -24, -25, -29, -31]) (countLit q [-32, -34, -35, -39, -40, -41, -42, -46, -48, -49, -51, -52, -56, -58, -59]) (count1560 q) 2 4 (meaning1488 q) (meaning1548 q) (meaning1565 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1548 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1548 = false ∨ valuation q 1565 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E187.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112187
