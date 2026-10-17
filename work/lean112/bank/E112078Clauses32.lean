import E112078Semantics
import B112E078Inputs
namespace Snake9.Regrowth.E112078
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-61, -63, -66]) + (countLit q [-67, -70, -72, -73]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66]) (l₂ := [-67, -70, -72, -73])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1593)) (countLit q [-61, -63, -66]) (countLit q [-67, -70, -72, -73]) (count1591 q) 2 1 (meaning1581 q) (meaning1587 q) (meaning1593 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1587 = false ∨ valuation q 1593 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1598)) (countLit q [-79]) (countLit q [-80]) (count1598 q) 1 (meaningNeg80 q) (meaning1598 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1598 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1598)) (countLit q [-79]) (countLit q [-80]) (count1598 q) 1 (meaningNeg79 q) (meaning1598 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1598 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 80 = true ∨ valuationOf q 1599 = true := by
  have hs : count1598 q = (countLit q [-79]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-80])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-80)) (literal (valuationOf q) (1599)) (countLit q [-79]) (countLit q [-80]) (count1598 q) 1 1 (meaningNeg79 q) (meaningNeg80 q) (meaning1599 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 80)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 80 = true ∨ valuation q 1599 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-75]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuationOf q) (1598)) (literal (valuationOf q) (1600)) (countLit q [-75]) (countLit q [-79, -80]) (count1600 q) 1 (meaning1598 q) (meaning1600 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1600 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-75]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79, -80])
  have hm := merge_right (literal (valuationOf q) (1599)) (literal (valuationOf q) (1601)) (countLit q [-75]) (countLit q [-79, -80]) (count1600 q) 2 (meaning1599 q) (meaning1601 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1601 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-75]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79, -80])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1600)) (countLit q [-75]) (countLit q [-79, -80]) (count1600 q) 1 (meaningNeg75 q) (meaning1600 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1600 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-75]) + (countLit q [-79, -80]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-79, -80])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1601)) (countLit q [-75]) (countLit q [-79, -80]) (count1600 q) 1 1 (meaningNeg75 q) (meaning1598 q) (meaning1601 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1598 = false ∨ valuation q 1601 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1603)) (countLit q [-81]) (countLit q [-82]) (count1603 q) 1 (meaningNeg82 q) (meaning1603 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1603 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1603 = true := by
  have hs : count1603 q = (countLit q [-81]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1603)) (countLit q [-81]) (countLit q [-82]) (count1603 q) 1 (meaningNeg81 q) (meaning1603 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1603 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1605)) (countLit q [-86]) (countLit q [-89]) (count1605 q) 1 (meaningNeg89 q) (meaning1605 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1605 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1605)) (countLit q [-86]) (countLit q [-89]) (count1605 q) 1 (meaningNeg86 q) (meaning1605 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1605 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-86]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1606)) (countLit q [-86]) (countLit q [-89]) (count1605 q) 1 1 (meaningNeg86 q) (meaningNeg89 q) (meaning1606 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 89 = true ∨ valuation q 1606 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1605 = false ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1605)) (literal (valuationOf q) (1607)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1607 q) 1 (meaning1605 q) (meaning1607 q) hs
  change valuationOf q 1605 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1605 = false ∨ valuation q 1607 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1608 = true := by
  have hs : count1607 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_right (literal (valuationOf q) (1606)) (literal (valuationOf q) (1608)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1607 q) 2 (meaning1606 q) (meaning1608 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1608 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1607 = true := by
  have hs : count1607 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_left (literal (valuationOf q) (1603)) (literal (valuationOf q) (1607)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1607 q) 1 (meaning1603 q) (meaning1607 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1607 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1608 = true := by
  have hs : count1607 q = (countLit q [-81, -82]) + (countLit q [-86, -89]) := List.countP_append (p := literal q) (l₁ := [-81, -82]) (l₂ := [-86, -89])
  have hm := merge_two (literal (valuationOf q) (1603)) (literal (valuationOf q) (1605)) (literal (valuationOf q) (1608)) (countLit q [-81, -82]) (countLit q [-86, -89]) (count1607 q) 1 1 (meaning1603 q) (meaning1605 q) (meaning1608 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1605 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1605 = false ∨ valuation q 1608 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1607)) (literal (valuationOf q) (1611)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1611 q) 1 (meaning1607 q) (meaning1611 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1611 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1608 = false ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_right (literal (valuationOf q) (1608)) (literal (valuationOf q) (1612)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1611 q) 2 (meaning1608 q) (meaning1612 q) hs
  change valuationOf q 1608 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1608 = false ∨ valuation q 1612 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1611 = true := by
  have hs : count1611 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1600)) (literal (valuationOf q) (1611)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1611 q) 1 (meaning1600 q) (meaning1611 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1611 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1607)) (literal (valuationOf q) (1612)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1611 q) 1 1 (meaning1600 q) (meaning1607 q) (meaning1612 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1607 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1607 = false ∨ valuation q 1612 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1613 = true := by
  have hs : count1611 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1600)) (literal (valuationOf q) (1608)) (literal (valuationOf q) (1613)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1611 q) 1 2 (meaning1600 q) (meaning1608 q) (meaning1613 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1608 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1608 = false ∨ valuation q 1613 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1612 = true := by
  have hs : count1611 q = (countLit q [-75, -79, -80]) + (countLit q [-81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-75, -79, -80]) (l₂ := [-81, -82, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1601)) (literal (valuationOf q) (1612)) (countLit q [-75, -79, -80]) (countLit q [-81, -82, -86, -89]) (count1611 q) 2 (meaning1601 q) (meaning1612 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1612 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1618 = true := by
  have hs : count1618 q = (countLit q [-61, -63, -66, -67, -70, -72, -73]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_left (literal (valuationOf q) (1591)) (literal (valuationOf q) (1618)) (countLit q [-61, -63, -66, -67, -70, -72, -73]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1618 q) 1 (meaning1591 q) (meaning1618 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1618 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1619 = true := by
  have hs : count1618 q = (countLit q [-61, -63, -66, -67, -70, -72, -73]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1619)) (countLit q [-61, -63, -66, -67, -70, -72, -73]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1618 q) 1 1 (meaning1591 q) (meaning1611 q) (meaning1619 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1611 = false ∨ valuation q 1619 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1620 = true := by
  have hs : count1618 q = (countLit q [-61, -63, -66, -67, -70, -72, -73]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1620)) (countLit q [-61, -63, -66, -67, -70, -72, -73]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1618 q) 1 2 (meaning1591 q) (meaning1612 q) (meaning1620 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1612 = false ∨ valuation q 1620 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1621 = true := by
  have hs : count1618 q = (countLit q [-61, -63, -66, -67, -70, -72, -73]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1591)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1621)) (countLit q [-61, -63, -66, -67, -70, -72, -73]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1618 q) 1 3 (meaning1591 q) (meaning1613 q) (meaning1621 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1613 = false ∨ valuation q 1621 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1620 = true := by
  have hs : count1618 q = (countLit q [-61, -63, -66, -67, -70, -72, -73]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1620)) (countLit q [-61, -63, -66, -67, -70, -72, -73]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1618 q) 2 1 (meaning1592 q) (meaning1611 q) (meaning1620 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1611 = false ∨ valuation q 1620 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1621 = true := by
  have hs : count1618 q = (countLit q [-61, -63, -66, -67, -70, -72, -73]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1612)) (literal (valuationOf q) (1621)) (countLit q [-61, -63, -66, -67, -70, -72, -73]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1618 q) 2 2 (meaning1592 q) (meaning1612 q) (meaning1621 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1612 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1612 = false ∨ valuation q 1621 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1622 = true := by
  have hs : count1618 q = (countLit q [-61, -63, -66, -67, -70, -72, -73]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1592)) (literal (valuationOf q) (1613)) (literal (valuationOf q) (1622)) (countLit q [-61, -63, -66, -67, -70, -72, -73]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1618 q) 2 3 (meaning1592 q) (meaning1613 q) (meaning1622 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1613 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1613 = false ∨ valuation q 1622 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1621 = true := by
  have hs : count1618 q = (countLit q [-61, -63, -66, -67, -70, -72, -73]) + (countLit q [-75, -79, -80, -81, -82, -86, -89]) := List.countP_append (p := literal q) (l₁ := [-61, -63, -66, -67, -70, -72, -73]) (l₂ := [-75, -79, -80, -81, -82, -86, -89])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1621)) (countLit q [-61, -63, -66, -67, -70, -72, -73]) (countLit q [-75, -79, -80, -81, -82, -86, -89]) (count1618 q) 3 1 (meaning1593 q) (meaning1611 q) (meaning1621 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1611 = false ∨ valuation q 1621 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1632 = true := by
  have hs : count1632 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1632)) (countLit q [-92]) (countLit q [-96]) (count1632 q) 1 (meaningNeg96 q) (meaning1632 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1632 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1632 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E078.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112078
