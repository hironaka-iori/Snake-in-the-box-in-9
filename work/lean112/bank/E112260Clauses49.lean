import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec49 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1569 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1038)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 4 3 (meaning1004 q) (meaning1026 q) (meaning1038 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1569 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1026 = false ∨ valuation q 1038 = true := counterClause1569 (baseVal q)

theorem counterClause1570 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1039)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 4 4 (meaning1004 q) (meaning1027 q) (meaning1039 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1570 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1027 = false ∨ valuation q 1039 = true := counterClause1570 (baseVal q)

theorem counterClause1571 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1040)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 4 5 (meaning1004 q) (meaning1028 q) (meaning1040 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1571 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1028 = false ∨ valuation q 1040 = true := counterClause1571 (baseVal q)

theorem counterClause1572 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1037)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 5 1 (meaning1005 q) (meaning1024 q) (meaning1037 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1572 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1024 = false ∨ valuation q 1037 = true := counterClause1572 (baseVal q)

theorem counterClause1573 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1038)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 5 2 (meaning1005 q) (meaning1025 q) (meaning1038 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1573 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1025 = false ∨ valuation q 1038 = true := counterClause1573 (baseVal q)

theorem counterClause1574 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1039)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 5 3 (meaning1005 q) (meaning1026 q) (meaning1039 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1574 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1026 = false ∨ valuation q 1039 = true := counterClause1574 (baseVal q)

theorem counterClause1575 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1040)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 5 4 (meaning1005 q) (meaning1027 q) (meaning1040 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1575 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1027 = false ∨ valuation q 1040 = true := counterClause1575 (baseVal q)

theorem counterClause1576 (q : Nat → Bool) : valuationOf q 1005 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1041 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1005)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1041)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 5 5 (meaning1005 q) (meaning1028 q) (meaning1041 q) hs
  change valuationOf q 1005 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1576 (q : Snake 81) (h : Conditions q) : valuation q 1005 = false ∨ valuation q 1028 = false ∨ valuation q 1041 = true := counterClause1576 (baseVal q)

theorem counterClause1577 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1039)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 6 2 (meaning1006 q) (meaning1025 q) (meaning1039 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1577 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1025 = false ∨ valuation q 1039 = true := counterClause1577 (baseVal q)

theorem counterClause1578 (q : Nat → Bool) : valuationOf q 1006 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1006)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1040)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 6 3 (meaning1006 q) (meaning1026 q) (meaning1040 q) hs
  change valuationOf q 1006 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1578 (q : Snake 81) (h : Conditions q) : valuation q 1006 = false ∨ valuation q 1026 = false ∨ valuation q 1040 = true := counterClause1578 (baseVal q)

theorem counterClause1579 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1047)) (countLit q [-96]) (countLit q [-98]) (count1047 q) 1 (meaningNeg98 q) (meaning1047 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1579 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1047 = true := counterClause1579 (baseVal q)

theorem counterClause1580 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1047)) (countLit q [-96]) (countLit q [-98]) (count1047 q) 1 (meaningNeg96 q) (meaning1047 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1580 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1047 = true := counterClause1580 (baseVal q)

theorem counterClause1581 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1048)) (countLit q [-96]) (countLit q [-98]) (count1047 q) 1 1 (meaningNeg96 q) (meaningNeg98 q) (meaning1048 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1581 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 98 = true ∨ valuation q 1048 = true := counterClause1581 (baseVal q)

theorem counterClause1582 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1049 = true := by
  have hs : count1049 q = (countLit q [-100]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1049)) (countLit q [-100]) (countLit q [-103]) (count1049 q) 1 (meaningNeg103 q) (meaning1049 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1582 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1049 = true := counterClause1582 (baseVal q)

theorem counterClause1583 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1049 = true := by
  have hs : count1049 q = (countLit q [-100]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-100)) (literal (valuationOf q) (1049)) (countLit q [-100]) (countLit q [-103]) (count1049 q) 1 (meaningNeg100 q) (meaning1049 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1583 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1049 = true := counterClause1583 (baseVal q)

theorem counterClause1584 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1050 = true := by
  have hs : count1049 q = (countLit q [-100]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-100]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-100)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1050)) (countLit q [-100]) (countLit q [-103]) (count1049 q) 1 1 (meaningNeg100 q) (meaningNeg103 q) (meaning1050 q) hs
  change (! (valuationOf q 100)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1584 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 103 = true ∨ valuation q 1050 = true := counterClause1584 (baseVal q)

theorem counterClause1585 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1051 = true := by
  have hs : count1051 q = (countLit q [-96, -98]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -103])
  have hm := merge_right (literal (valuationOf q) (1049)) (literal (valuationOf q) (1051)) (countLit q [-96, -98]) (countLit q [-100, -103]) (count1051 q) 1 (meaning1049 q) (meaning1051 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1585 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1051 = true := counterClause1585 (baseVal q)

theorem counterClause1586 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-96, -98]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -103])
  have hm := merge_right (literal (valuationOf q) (1050)) (literal (valuationOf q) (1052)) (countLit q [-96, -98]) (countLit q [-100, -103]) (count1051 q) 2 (meaning1050 q) (meaning1052 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1586 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1052 = true := counterClause1586 (baseVal q)

theorem counterClause1587 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1051 = true := by
  have hs : count1051 q = (countLit q [-96, -98]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -103])
  have hm := merge_left (literal (valuationOf q) (1047)) (literal (valuationOf q) (1051)) (countLit q [-96, -98]) (countLit q [-100, -103]) (count1051 q) 1 (meaning1047 q) (meaning1051 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1587 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1051 = true := counterClause1587 (baseVal q)

theorem counterClause1588 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-96, -98]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -103])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1049)) (literal (valuationOf q) (1052)) (countLit q [-96, -98]) (countLit q [-100, -103]) (count1051 q) 1 1 (meaning1047 q) (meaning1049 q) (meaning1052 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1588 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1049 = false ∨ valuation q 1052 = true := counterClause1588 (baseVal q)

theorem counterClause1589 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1053 = true := by
  have hs : count1051 q = (countLit q [-96, -98]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -103])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1053)) (countLit q [-96, -98]) (countLit q [-100, -103]) (count1051 q) 1 2 (meaning1047 q) (meaning1050 q) (meaning1053 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1589 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1050 = false ∨ valuation q 1053 = true := counterClause1589 (baseVal q)

theorem counterClause1590 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-96, -98]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -103])
  have hm := merge_left (literal (valuationOf q) (1048)) (literal (valuationOf q) (1052)) (countLit q [-96, -98]) (countLit q [-100, -103]) (count1051 q) 2 (meaning1048 q) (meaning1052 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1590 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1052 = true := counterClause1590 (baseVal q)

theorem counterClause1591 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1053 = true := by
  have hs : count1051 q = (countLit q [-96, -98]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -103])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1049)) (literal (valuationOf q) (1053)) (countLit q [-96, -98]) (countLit q [-100, -103]) (count1051 q) 2 1 (meaning1048 q) (meaning1049 q) (meaning1053 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1591 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1049 = false ∨ valuation q 1053 = true := counterClause1591 (baseVal q)

theorem counterClause1592 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1054 = true := by
  have hs : count1051 q = (countLit q [-96, -98]) + (countLit q [-100, -103]) := List.countP_append (p := literal q) (l₁ := [-96, -98]) (l₂ := [-100, -103])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1054)) (countLit q [-96, -98]) (countLit q [-100, -103]) (count1051 q) 2 2 (meaning1048 q) (meaning1050 q) (meaning1054 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1592 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1050 = false ∨ valuation q 1054 = true := counterClause1592 (baseVal q)

theorem counterClause1593 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1055 = true := by
  have hs : count1055 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1055)) (countLit q [-105]) (countLit q [-108]) (count1055 q) 1 (meaningNeg108 q) (meaning1055 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1593 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1055 = true := counterClause1593 (baseVal q)

theorem counterClause1594 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1055 = true := by
  have hs : count1055 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-105)) (literal (valuationOf q) (1055)) (countLit q [-105]) (countLit q [-108]) (count1055 q) 1 (meaningNeg105 q) (meaning1055 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1594 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1055 = true := counterClause1594 (baseVal q)

theorem counterClause1595 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 108 = true ∨ valuationOf q 1056 = true := by
  have hs : count1055 q = (countLit q [-105]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-105]) (l₂ := [-108])
  have hm := merge_two (literal (valuationOf q) (-105)) (literal (valuationOf q) (-108)) (literal (valuationOf q) (1056)) (countLit q [-105]) (countLit q [-108]) (count1055 q) 1 1 (meaningNeg105 q) (meaningNeg108 q) (meaning1056 q) hs
  change (! (valuationOf q 105)) = false ∨ (! (valuationOf q 108)) = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1595 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 108 = true ∨ valuation q 1056 = true := counterClause1595 (baseVal q)

theorem counterClause1596 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1057 = true := by
  have hs : count1057 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_right (literal (valuationOf q) (-111)) (literal (valuationOf q) (1057)) (countLit q [-110]) (countLit q [-111]) (count1057 q) 1 (meaningNeg111 q) (meaning1057 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1596 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1057 = true := counterClause1596 (baseVal q)

theorem counterClause1597 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 1057 = true := by
  have hs : count1057 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_left (literal (valuationOf q) (-110)) (literal (valuationOf q) (1057)) (countLit q [-110]) (countLit q [-111]) (count1057 q) 1 (meaningNeg110 q) (meaning1057 q) hs
  change (! (valuationOf q 110)) = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1597 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 1057 = true := counterClause1597 (baseVal q)

theorem counterClause1598 (q : Nat → Bool) : valuationOf q 110 = true ∨ valuationOf q 111 = true ∨ valuationOf q 1058 = true := by
  have hs : count1057 q = (countLit q [-110]) + (countLit q [-111]) := List.countP_append (p := literal q) (l₁ := [-110]) (l₂ := [-111])
  have hm := merge_two (literal (valuationOf q) (-110)) (literal (valuationOf q) (-111)) (literal (valuationOf q) (1058)) (countLit q [-110]) (countLit q [-111]) (count1057 q) 1 1 (meaningNeg110 q) (meaningNeg111 q) (meaning1058 q) hs
  change (! (valuationOf q 110)) = false ∨ (! (valuationOf q 111)) = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1598 (q : Snake 81) (h : Conditions q) : valuation q 110 = true ∨ valuation q 111 = true ∨ valuation q 1058 = true := counterClause1598 (baseVal q)

theorem counterClause1599 (q : Nat → Bool) : valuationOf q 1057 = false ∨ valuationOf q 1059 = true := by
  have hs : count1059 q = (countLit q [-105, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-105, -108]) (l₂ := [-110, -111])
  have hm := merge_right (literal (valuationOf q) (1057)) (literal (valuationOf q) (1059)) (countLit q [-105, -108]) (countLit q [-110, -111]) (count1059 q) 1 (meaning1057 q) (meaning1059 q) hs
  change valuationOf q 1057 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1599 (q : Snake 81) (h : Conditions q) : valuation q 1057 = false ∨ valuation q 1059 = true := counterClause1599 (baseVal q)

theorem counterClause1600 (q : Nat → Bool) : valuationOf q 1058 = false ∨ valuationOf q 1060 = true := by
  have hs : count1059 q = (countLit q [-105, -108]) + (countLit q [-110, -111]) := List.countP_append (p := literal q) (l₁ := [-105, -108]) (l₂ := [-110, -111])
  have hm := merge_right (literal (valuationOf q) (1058)) (literal (valuationOf q) (1060)) (countLit q [-105, -108]) (countLit q [-110, -111]) (count1059 q) 2 (meaning1058 q) (meaning1060 q) hs
  change valuationOf q 1058 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1600 (q : Snake 81) (h : Conditions q) : valuation q 1058 = false ∨ valuation q 1060 = true := counterClause1600 (baseVal q)

theorem block49 (q : Snake 81) (h : Conditions q) : B112E260.Block49 (valuation q) :=
  ⟨clause1569 q h, clause1570 q h, clause1571 q h, clause1572 q h, clause1573 q h, clause1574 q h, clause1575 q h, clause1576 q h, clause1577 q h, clause1578 q h, clause1579 q h, clause1580 q h, clause1581 q h, clause1582 q h, clause1583 q h, clause1584 q h, clause1585 q h, clause1586 q h, clause1587 q h, clause1588 q h, clause1589 q h, clause1590 q h, clause1591 q h, clause1592 q h, clause1593 q h, clause1594 q h, clause1595 q h, clause1596 q h, clause1597 q h, clause1598 q h, clause1599 q h, clause1600 q h⟩

end
end Snake9.Regrowth.E112260
