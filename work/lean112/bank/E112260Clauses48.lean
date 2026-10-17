import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec48 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1537 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1028)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 3 2 (meaning1014 q) (meaning1021 q) (meaning1028 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1537 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1021 = false ∨ valuation q 1028 = true := counterClause1537 (baseVal q)

theorem counterClause1538 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1029)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 3 3 (meaning1014 q) (meaning1022 q) (meaning1029 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1538 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1022 = false ∨ valuation q 1029 = true := counterClause1538 (baseVal q)

theorem counterClause1539 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1030 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1030)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 3 4 (meaning1014 q) (meaning1023 q) (meaning1030 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1539 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1023 = false ∨ valuation q 1030 = true := counterClause1539 (baseVal q)

theorem counterClause1540 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1032 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1024)) (literal (valuationOf q) (1032)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 1 (meaning1024 q) (meaning1032 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1540 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1032 = true := counterClause1540 (baseVal q)

theorem counterClause1541 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1025)) (literal (valuationOf q) (1033)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 2 (meaning1025 q) (meaning1033 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1541 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1033 = true := counterClause1541 (baseVal q)

theorem counterClause1542 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1026)) (literal (valuationOf q) (1034)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 3 (meaning1026 q) (meaning1034 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1542 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1034 = true := counterClause1542 (baseVal q)

theorem counterClause1543 (q : Nat → Bool) : valuationOf q 1027 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1027)) (literal (valuationOf q) (1035)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 4 (meaning1027 q) (meaning1035 q) hs
  change valuationOf q 1027 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1543 (q : Snake 81) (h : Conditions q) : valuation q 1027 = false ∨ valuation q 1035 = true := counterClause1543 (baseVal q)

theorem counterClause1544 (q : Nat → Bool) : valuationOf q 1028 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1028)) (literal (valuationOf q) (1036)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 5 (meaning1028 q) (meaning1036 q) hs
  change valuationOf q 1028 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1544 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false ∨ valuation q 1036 = true := counterClause1544 (baseVal q)

theorem counterClause1545 (q : Nat → Bool) : valuationOf q 1029 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1029)) (literal (valuationOf q) (1037)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 6 (meaning1029 q) (meaning1037 q) hs
  change valuationOf q 1029 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1545 (q : Snake 81) (h : Conditions q) : valuation q 1029 = false ∨ valuation q 1037 = true := counterClause1545 (baseVal q)

theorem counterClause1546 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1033)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 1 1 (meaning1001 q) (meaning1024 q) (meaning1033 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1546 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1024 = false ∨ valuation q 1033 = true := counterClause1546 (baseVal q)

theorem counterClause1547 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1034)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 1 2 (meaning1001 q) (meaning1025 q) (meaning1034 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1547 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1025 = false ∨ valuation q 1034 = true := counterClause1547 (baseVal q)

theorem counterClause1548 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1035)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 1 3 (meaning1001 q) (meaning1026 q) (meaning1035 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1548 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1026 = false ∨ valuation q 1035 = true := counterClause1548 (baseVal q)

theorem counterClause1549 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1036)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 1 4 (meaning1001 q) (meaning1027 q) (meaning1036 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1549 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1027 = false ∨ valuation q 1036 = true := counterClause1549 (baseVal q)

theorem counterClause1550 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1037)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 1 5 (meaning1001 q) (meaning1028 q) (meaning1037 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1550 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1028 = false ∨ valuation q 1037 = true := counterClause1550 (baseVal q)

theorem counterClause1551 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1038)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 1 6 (meaning1001 q) (meaning1029 q) (meaning1038 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1551 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1029 = false ∨ valuation q 1038 = true := counterClause1551 (baseVal q)

theorem counterClause1552 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_left (literal (valuationOf q) (1002)) (literal (valuationOf q) (1033)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 2 (meaning1002 q) (meaning1033 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1552 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1033 = true := counterClause1552 (baseVal q)

theorem counterClause1553 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1034)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 2 1 (meaning1002 q) (meaning1024 q) (meaning1034 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1553 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1024 = false ∨ valuation q 1034 = true := counterClause1553 (baseVal q)

theorem counterClause1554 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1035)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 2 2 (meaning1002 q) (meaning1025 q) (meaning1035 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1554 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1025 = false ∨ valuation q 1035 = true := counterClause1554 (baseVal q)

theorem counterClause1555 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1036)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 2 3 (meaning1002 q) (meaning1026 q) (meaning1036 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1555 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1026 = false ∨ valuation q 1036 = true := counterClause1555 (baseVal q)

theorem counterClause1556 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1037)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 2 4 (meaning1002 q) (meaning1027 q) (meaning1037 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1556 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1027 = false ∨ valuation q 1037 = true := counterClause1556 (baseVal q)

theorem counterClause1557 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1038)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 2 5 (meaning1002 q) (meaning1028 q) (meaning1038 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1557 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1028 = false ∨ valuation q 1038 = true := counterClause1557 (baseVal q)

theorem counterClause1558 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1039)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 2 6 (meaning1002 q) (meaning1029 q) (meaning1039 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1558 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1029 = false ∨ valuation q 1039 = true := counterClause1558 (baseVal q)

theorem counterClause1559 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1040)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 2 7 (meaning1002 q) (meaning1030 q) (meaning1040 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1559 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1030 = false ∨ valuation q 1040 = true := counterClause1559 (baseVal q)

theorem counterClause1560 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1035)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 3 1 (meaning1003 q) (meaning1024 q) (meaning1035 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1560 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1024 = false ∨ valuation q 1035 = true := counterClause1560 (baseVal q)

theorem counterClause1561 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1036)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 3 2 (meaning1003 q) (meaning1025 q) (meaning1036 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1561 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1025 = false ∨ valuation q 1036 = true := counterClause1561 (baseVal q)

theorem counterClause1562 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1037)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 3 3 (meaning1003 q) (meaning1026 q) (meaning1037 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1562 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1026 = false ∨ valuation q 1037 = true := counterClause1562 (baseVal q)

theorem counterClause1563 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1038)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 3 4 (meaning1003 q) (meaning1027 q) (meaning1038 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1563 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1027 = false ∨ valuation q 1038 = true := counterClause1563 (baseVal q)

theorem counterClause1564 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1039 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1039)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 3 5 (meaning1003 q) (meaning1028 q) (meaning1039 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1564 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1028 = false ∨ valuation q 1039 = true := counterClause1564 (baseVal q)

theorem counterClause1565 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1040 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1040)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 3 6 (meaning1003 q) (meaning1029 q) (meaning1040 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1565 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1029 = false ∨ valuation q 1040 = true := counterClause1565 (baseVal q)

theorem counterClause1566 (q : Nat → Bool) : valuationOf q 1003 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1041 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1003)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1041)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 3 7 (meaning1003 q) (meaning1030 q) (meaning1041 q) hs
  change valuationOf q 1003 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1566 (q : Snake 81) (h : Conditions q) : valuation q 1003 = false ∨ valuation q 1030 = false ∨ valuation q 1041 = true := counterClause1566 (baseVal q)

theorem counterClause1567 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1036)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 4 1 (meaning1004 q) (meaning1024 q) (meaning1036 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1567 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1024 = false ∨ valuation q 1036 = true := counterClause1567 (baseVal q)

theorem counterClause1568 (q : Nat → Bool) : valuationOf q 1004 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-65, -67, -68, -69, -72, -73, -74]) + (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -68, -69, -72, -73, -74]) (l₂ := [-76, -79, -81, -82, -85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1004)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1037)) (countLit q [-65, -67, -68, -69, -72, -73, -74]) (countLit q [-76, -79, -81, -82, -85, -86, -89, -90]) (count1032 q) 4 2 (meaning1004 q) (meaning1025 q) (meaning1037 q) hs
  change valuationOf q 1004 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1568 (q : Snake 81) (h : Conditions q) : valuation q 1004 = false ∨ valuation q 1025 = false ∨ valuation q 1037 = true := counterClause1568 (baseVal q)

theorem block48 (q : Snake 81) (h : Conditions q) : B112E260.Block48 (valuation q) :=
  ⟨clause1537 q h, clause1538 q h, clause1539 q h, clause1540 q h, clause1541 q h, clause1542 q h, clause1543 q h, clause1544 q h, clause1545 q h, clause1546 q h, clause1547 q h, clause1548 q h, clause1549 q h, clause1550 q h, clause1551 q h, clause1552 q h, clause1553 q h, clause1554 q h, clause1555 q h, clause1556 q h, clause1557 q h, clause1558 q h, clause1559 q h, clause1560 q h, clause1561 q h, clause1562 q h, clause1563 q h, clause1564 q h, clause1565 q h, clause1566 q h, clause1567 q h, clause1568 q h⟩

end
end Snake9.Regrowth.E112260
