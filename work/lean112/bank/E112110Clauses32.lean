import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1573)) (countLit q [-77]) (countLit q [-78]) (count1573 q) 1 (meaningNeg78 q) (meaning1573 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1573 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1573 = true := by
  have hs : count1573 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1573)) (countLit q [-77]) (countLit q [-78]) (count1573 q) 1 (meaningNeg77 q) (meaning1573 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1573 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 78 = true ∨ valuationOf q 1574 = true := by
  have hs : count1573 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-78)) (literal (valuationOf q) (1574)) (countLit q [-77]) (countLit q [-78]) (count1573 q) 1 1 (meaningNeg77 q) (meaningNeg78 q) (meaning1574 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 78)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 78 = true ∨ valuation q 1574 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1573)) (literal (valuationOf q) (1575)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 1 (meaning1573 q) (meaning1575 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1575 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1574)) (literal (valuationOf q) (1576)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 2 (meaning1574 q) (meaning1576 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1576 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1571)) (literal (valuationOf q) (1575)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 1 (meaning1571 q) (meaning1575 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1575 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1576)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 1 1 (meaning1571 q) (meaning1573 q) (meaning1576 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1573 = false ∨ valuation q 1576 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1571 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1571)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1577)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 1 2 (meaning1571 q) (meaning1574 q) (meaning1577 q) hs
  change valuationOf q 1571 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1571 = false ∨ valuation q 1574 = false ∨ valuation q 1577 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1576 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1572)) (literal (valuationOf q) (1576)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 2 (meaning1572 q) (meaning1576 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1576 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1577 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1573)) (literal (valuationOf q) (1577)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 2 1 (meaning1572 q) (meaning1573 q) (meaning1577 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1573 = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1573 = false ∨ valuation q 1577 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1578 = true := by
  have hs : count1575 q = (countLit q [-72, -73]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1574)) (literal (valuationOf q) (1578)) (countLit q [-72, -73]) (countLit q [-77, -78]) (count1575 q) 2 2 (meaning1572 q) (meaning1574 q) (meaning1578 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1574 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1574 = false ∨ valuation q 1578 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-79]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1579)) (countLit q [-79]) (countLit q [-82]) (count1579 q) 1 (meaningNeg82 q) (meaning1579 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1579 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-79]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1579)) (countLit q [-79]) (countLit q [-82]) (count1579 q) 1 (meaningNeg79 q) (meaning1579 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1579 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-79]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1580)) (countLit q [-79]) (countLit q [-82]) (count1579 q) 1 1 (meaningNeg79 q) (meaningNeg82 q) (meaning1580 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 82 = true ∨ valuation q 1580 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1581)) (countLit q [-84]) (countLit q [-86]) (count1581 q) 1 (meaningNeg86 q) (meaning1581 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1581 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1581 = true := by
  have hs : count1581 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1581)) (countLit q [-84]) (countLit q [-86]) (count1581 q) 1 (meaningNeg84 q) (meaning1581 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1581 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1581 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1582 = true := by
  have hs : count1581 q = (countLit q [-84]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1582)) (countLit q [-84]) (countLit q [-86]) (count1581 q) 1 1 (meaningNeg84 q) (meaningNeg86 q) (meaning1582 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 86 = true ∨ valuation q 1582 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-79, -82]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-84, -86])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (countLit q [-79, -82]) (countLit q [-84, -86]) (count1583 q) 1 (meaning1581 q) (meaning1583 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-79, -82]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-84, -86])
  have hm := merge_right (literal (valuationOf q) (1582)) (literal (valuationOf q) (1584)) (countLit q [-79, -82]) (countLit q [-84, -86]) (count1583 q) 2 (meaning1582 q) (meaning1584 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1584 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-79, -82]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-84, -86])
  have hm := merge_left (literal (valuationOf q) (1579)) (literal (valuationOf q) (1583)) (countLit q [-79, -82]) (countLit q [-84, -86]) (count1583 q) 1 (meaning1579 q) (meaning1583 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1583 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-79, -82]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-84, -86])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-79, -82]) (countLit q [-84, -86]) (count1583 q) 1 1 (meaning1579 q) (meaning1581 q) (meaning1584 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-79, -82]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-84, -86])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1585)) (countLit q [-79, -82]) (countLit q [-84, -86]) (count1583 q) 1 2 (meaning1579 q) (meaning1582 q) (meaning1585 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1582 = false ∨ valuation q 1585 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-79, -82]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-84, -86])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1584)) (countLit q [-79, -82]) (countLit q [-84, -86]) (count1583 q) 2 (meaning1580 q) (meaning1584 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1584 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1585 = true := by
  have hs : count1583 q = (countLit q [-79, -82]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-84, -86])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1585)) (countLit q [-79, -82]) (countLit q [-84, -86]) (count1583 q) 2 1 (meaning1580 q) (meaning1581 q) (meaning1585 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1581 = false ∨ valuation q 1585 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1586 = true := by
  have hs : count1583 q = (countLit q [-79, -82]) + (countLit q [-84, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -82]) (l₂ := [-84, -86])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1582)) (literal (valuationOf q) (1586)) (countLit q [-79, -82]) (countLit q [-84, -86]) (count1583 q) 2 2 (meaning1580 q) (meaning1582 q) (meaning1586 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1582 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1582 = false ∨ valuation q 1586 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_right (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 1 (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1587 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_right (literal (valuationOf q) (1584)) (literal (valuationOf q) (1588)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 2 (meaning1584 q) (meaning1588 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1588 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_right (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 3 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_right (literal (valuationOf q) (1586)) (literal (valuationOf q) (1590)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 4 (meaning1586 q) (meaning1590 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1590 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1587)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 1 (meaning1575 q) (meaning1587 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1587 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1588)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 1 1 (meaning1575 q) (meaning1583 q) (meaning1588 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1583 = false ∨ valuation q 1588 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-72, -73, -77, -78]) + (countLit q [-79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-72, -73, -77, -78]) (l₂ := [-79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1584)) (literal (valuationOf q) (1589)) (countLit q [-72, -73, -77, -78]) (countLit q [-79, -82, -84, -86]) (count1587 q) 1 2 (meaning1575 q) (meaning1584 q) (meaning1589 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1584 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1584 = false ∨ valuation q 1589 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E110.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112110
