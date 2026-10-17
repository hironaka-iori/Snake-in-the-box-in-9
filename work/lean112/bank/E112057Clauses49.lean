import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1037 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_left (literal (valuationOf q) (1025)) (literal (valuationOf q) (1037)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 3 (meaning1025 q) (meaning1037 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1037 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1038 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1025)) (literal (valuationOf q) (1031)) (literal (valuationOf q) (1038)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 3 1 (meaning1025 q) (meaning1031 q) (meaning1038 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1031 = false ∨ valuation q 1038 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1039 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1025)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1039)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 3 2 (meaning1025 q) (meaning1032 q) (meaning1039 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1032 = false ∨ valuation q 1039 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1040 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1025)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1040)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 3 3 (meaning1025 q) (meaning1033 q) (meaning1040 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1033 = false ∨ valuation q 1040 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1041 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1025)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1041)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 3 4 (meaning1025 q) (meaning1034 q) (meaning1041 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1034 = false ∨ valuation q 1041 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1038 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_left (literal (valuationOf q) (1026)) (literal (valuationOf q) (1038)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 4 (meaning1026 q) (meaning1038 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1038 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1039 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1026)) (literal (valuationOf q) (1031)) (literal (valuationOf q) (1039)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 4 1 (meaning1026 q) (meaning1031 q) (meaning1039 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1031 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1031 = false ∨ valuation q 1039 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1040 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1026)) (literal (valuationOf q) (1032)) (literal (valuationOf q) (1040)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 4 2 (meaning1026 q) (meaning1032 q) (meaning1040 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1032 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1032 = false ∨ valuation q 1040 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1041 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1026)) (literal (valuationOf q) (1033)) (literal (valuationOf q) (1041)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 4 3 (meaning1026 q) (meaning1033 q) (meaning1041 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1033 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1033 = false ∨ valuation q 1041 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1042 = true := by
  have hs : count1035 q = (countLit q [-65, -67, -69, -72]) + (countLit q [-73, -75, -77, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -69, -72]) (l₂ := [-73, -75, -77, -79])
  have hm := merge_two (literal (valuationOf q) (1026)) (literal (valuationOf q) (1034)) (literal (valuationOf q) (1042)) (countLit q [-65, -67, -69, -72]) (countLit q [-73, -75, -77, -79]) (count1035 q) 4 4 (meaning1026 q) (meaning1034 q) (meaning1042 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1034 = false ∨ valuationOf q 1042 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1034 = false ∨ valuation q 1042 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1043 = true := by
  have hs : count1043 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1043)) (countLit q [-82]) (countLit q [-83]) (count1043 q) 1 (meaningNeg83 q) (meaning1043 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1043 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1043 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1043 = true := by
  have hs : count1043 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1043)) (countLit q [-82]) (countLit q [-83]) (count1043 q) 1 (meaningNeg82 q) (meaning1043 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1043 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1043 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 83 = true ∨ valuationOf q 1044 = true := by
  have hs : count1043 q = (countLit q [-82]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-83])
  have hm := merge_two (literal (valuationOf q) (-82)) (literal (valuationOf q) (-83)) (literal (valuationOf q) (1044)) (countLit q [-82]) (countLit q [-83]) (count1043 q) 1 1 (meaningNeg82 q) (meaningNeg83 q) (meaning1044 q) hs
  change (! (valuationOf q 82)) = false ∨ (! (valuationOf q 83)) = false ∨ valuationOf q 1044 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 83 = true ∨ valuation q 1044 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1045 = true := by
  have hs : count1045 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1045)) (countLit q [-86]) (countLit q [-87]) (count1045 q) 1 (meaningNeg87 q) (meaning1045 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1045 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1045 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1045 = true := by
  have hs : count1045 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1045)) (countLit q [-86]) (countLit q [-87]) (count1045 q) 1 (meaningNeg86 q) (meaning1045 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1045 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1045 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1046 = true := by
  have hs : count1045 q = (countLit q [-86]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-86)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1046)) (countLit q [-86]) (countLit q [-87]) (count1045 q) 1 1 (meaningNeg86 q) (meaningNeg87 q) (meaning1046 q) hs
  change (! (valuationOf q 86)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1046 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 87 = true ∨ valuation q 1046 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 1045 = false ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-82, -83]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1045)) (literal (valuationOf q) (1047)) (countLit q [-82, -83]) (countLit q [-86, -87]) (count1047 q) 1 (meaning1045 q) (meaning1047 q) hs
  change valuationOf q 1045 = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 1045 = false ∨ valuation q 1047 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 1046 = false ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-82, -83]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -87])
  have hm := merge_right (literal (valuationOf q) (1046)) (literal (valuationOf q) (1048)) (countLit q [-82, -83]) (countLit q [-86, -87]) (count1047 q) 2 (meaning1046 q) (meaning1048 q) hs
  change valuationOf q 1046 = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 1046 = false ∨ valuation q 1048 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 1043 = false ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-82, -83]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -87])
  have hm := merge_left (literal (valuationOf q) (1043)) (literal (valuationOf q) (1047)) (countLit q [-82, -83]) (countLit q [-86, -87]) (count1047 q) 1 (meaning1043 q) (meaning1047 q) hs
  change valuationOf q 1043 = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 1043 = false ∨ valuation q 1047 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 1043 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-82, -83]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1043)) (literal (valuationOf q) (1045)) (literal (valuationOf q) (1048)) (countLit q [-82, -83]) (countLit q [-86, -87]) (count1047 q) 1 1 (meaning1043 q) (meaning1045 q) (meaning1048 q) hs
  change valuationOf q 1043 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 1043 = false ∨ valuation q 1045 = false ∨ valuation q 1048 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 1043 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1049 = true := by
  have hs : count1047 q = (countLit q [-82, -83]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1043)) (literal (valuationOf q) (1046)) (literal (valuationOf q) (1049)) (countLit q [-82, -83]) (countLit q [-86, -87]) (count1047 q) 1 2 (meaning1043 q) (meaning1046 q) (meaning1049 q) hs
  change valuationOf q 1043 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 1043 = false ∨ valuation q 1046 = false ∨ valuation q 1049 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1044 = false ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-82, -83]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -87])
  have hm := merge_left (literal (valuationOf q) (1044)) (literal (valuationOf q) (1048)) (countLit q [-82, -83]) (countLit q [-86, -87]) (count1047 q) 2 (meaning1044 q) (meaning1048 q) hs
  change valuationOf q 1044 = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1044 = false ∨ valuation q 1048 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1044 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1049 = true := by
  have hs : count1047 q = (countLit q [-82, -83]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1044)) (literal (valuationOf q) (1045)) (literal (valuationOf q) (1049)) (countLit q [-82, -83]) (countLit q [-86, -87]) (count1047 q) 2 1 (meaning1044 q) (meaning1045 q) (meaning1049 q) hs
  change valuationOf q 1044 = false ∨ valuationOf q 1045 = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1044 = false ∨ valuation q 1045 = false ∨ valuation q 1049 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 1044 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1050 = true := by
  have hs : count1047 q = (countLit q [-82, -83]) + (countLit q [-86, -87]) := List.countP_append (p := literal q) (l₁ := [-82, -83]) (l₂ := [-86, -87])
  have hm := merge_two (literal (valuationOf q) (1044)) (literal (valuationOf q) (1046)) (literal (valuationOf q) (1050)) (countLit q [-82, -83]) (countLit q [-86, -87]) (count1047 q) 2 2 (meaning1044 q) (meaning1046 q) (meaning1050 q) hs
  change valuationOf q 1044 = false ∨ valuationOf q 1046 = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 1044 = false ∨ valuation q 1046 = false ∨ valuation q 1050 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1051 = true := by
  have hs : count1051 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1051)) (countLit q [-89]) (countLit q [-90]) (count1051 q) 1 (meaningNeg90 q) (meaning1051 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1051 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1051 = true := by
  have hs : count1051 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1051)) (countLit q [-89]) (countLit q [-90]) (count1051 q) 1 (meaningNeg89 q) (meaning1051 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1051 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1052)) (countLit q [-89]) (countLit q [-90]) (count1051 q) 1 1 (meaningNeg89 q) (meaningNeg90 q) (meaning1052 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 90 = true ∨ valuation q 1052 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1053 = true := by
  have hs : count1053 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_right (literal (valuationOf q) (-94)) (literal (valuationOf q) (1053)) (countLit q [-91]) (countLit q [-94]) (count1053 q) 1 (meaningNeg94 q) (meaning1053 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1053 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1053 = true := by
  have hs : count1053 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1053)) (countLit q [-91]) (countLit q [-94]) (count1053 q) 1 (meaningNeg91 q) (meaning1053 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1053 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 94 = true ∨ valuationOf q 1054 = true := by
  have hs : count1053 q = (countLit q [-91]) + (countLit q [-94]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-94])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (-94)) (literal (valuationOf q) (1054)) (countLit q [-91]) (countLit q [-94]) (count1053 q) 1 1 (meaningNeg91 q) (meaningNeg94 q) (meaning1054 q) hs
  change (! (valuationOf q 91)) = false ∨ (! (valuationOf q 94)) = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 94 = true ∨ valuation q 1054 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1055 = true := by
  have hs : count1055 q = (countLit q [-89, -90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-91, -94])
  have hm := merge_right (literal (valuationOf q) (1053)) (literal (valuationOf q) (1055)) (countLit q [-89, -90]) (countLit q [-91, -94]) (count1055 q) 1 (meaning1053 q) (meaning1055 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1055 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 1054 = false ∨ valuationOf q 1056 = true := by
  have hs : count1055 q = (countLit q [-89, -90]) + (countLit q [-91, -94]) := List.countP_append (p := literal q) (l₁ := [-89, -90]) (l₂ := [-91, -94])
  have hm := merge_right (literal (valuationOf q) (1054)) (literal (valuationOf q) (1056)) (countLit q [-89, -90]) (countLit q [-91, -94]) (count1055 q) 2 (meaning1054 q) (meaning1056 q) hs
  change valuationOf q 1054 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 1054 = false ∨ valuation q 1056 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E057.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112057
