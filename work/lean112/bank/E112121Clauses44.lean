import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 1024 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1030 = true := by
  have hs : count1027 q = (countLit q [-71, -74]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-71, -74]) (l₂ := [-77, -78])
  have hm := merge_two (literal (valuationOf q) (1024)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1030)) (countLit q [-71, -74]) (countLit q [-77, -78]) (count1027 q) 2 2 (meaning1024 q) (meaning1026 q) (meaning1030 q) hs
  change valuationOf q 1024 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1030 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 1024 = false ∨ valuation q 1026 = false ∨ valuation q 1030 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 1027 = false ∨ valuationOf q 1031 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1027)) (literal (valuationOf q) (1031)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 1 (meaning1027 q) (meaning1031 q) hs
  change valuationOf q 1027 = false ∨ valuationOf q 1031 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 1027 = false ∨ valuation q 1031 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 1028 = false ∨ valuationOf q 1032 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1028)) (literal (valuationOf q) (1032)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 2 (meaning1028 q) (meaning1032 q) hs
  change valuationOf q 1028 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false ∨ valuation q 1032 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 1029 = false ∨ valuationOf q 1033 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1029)) (literal (valuationOf q) (1033)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 3 (meaning1029 q) (meaning1033 q) hs
  change valuationOf q 1029 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 1029 = false ∨ valuation q 1033 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 1030 = false ∨ valuationOf q 1034 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_right (literal (valuationOf q) (1030)) (literal (valuationOf q) (1034)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 4 (meaning1030 q) (meaning1034 q) hs
  change valuationOf q 1030 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 1030 = false ∨ valuation q 1034 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1031 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_left (literal (valuationOf q) (1019)) (literal (valuationOf q) (1031)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 1 (meaning1019 q) (meaning1031 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1031 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1031 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1032 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1032)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 1 1 (meaning1019 q) (meaning1027 q) (meaning1032 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1027 = false ∨ valuation q 1032 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1033 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1033)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 1 2 (meaning1019 q) (meaning1028 q) (meaning1033 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1028 = false ∨ valuation q 1033 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1034 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1034)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 1 3 (meaning1019 q) (meaning1029 q) (meaning1034 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1029 = false ∨ valuation q 1034 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 1019 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1035 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1019)) (literal (valuationOf q) (1030)) (literal (valuationOf q) (1035)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 1 4 (meaning1019 q) (meaning1030 q) (meaning1035 q) hs
  change valuationOf q 1019 = false ∨ valuationOf q 1030 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 1019 = false ∨ valuation q 1030 = false ∨ valuation q 1035 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1032 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_left (literal (valuationOf q) (1020)) (literal (valuationOf q) (1032)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 2 (meaning1020 q) (meaning1032 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1032 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1032 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1033 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1033)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 2 1 (meaning1020 q) (meaning1027 q) (meaning1033 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1027 = false ∨ valuation q 1033 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1034 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1034)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 2 2 (meaning1020 q) (meaning1028 q) (meaning1034 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1028 = false ∨ valuation q 1034 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1035 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1020)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1035)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 2 3 (meaning1020 q) (meaning1029 q) (meaning1035 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1029 = false ∨ valuation q 1035 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1034 = true := by
  have hs : count1031 q = (countLit q [-63, -66, -68, -69]) + (countLit q [-71, -74, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69]) (l₂ := [-71, -74, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1021)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1034)) (countLit q [-63, -66, -68, -69]) (countLit q [-71, -74, -77, -78]) (count1031 q) 3 1 (meaning1021 q) (meaning1027 q) (meaning1034 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1027 = false ∨ valuation q 1034 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1039 = true := by
  have hs : count1039 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_right (literal (valuationOf q) (-81)) (literal (valuationOf q) (1039)) (countLit q [-79]) (countLit q [-81]) (count1039 q) 1 (meaningNeg81 q) (meaning1039 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1039 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1039 = true := by
  have hs : count1039 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_left (literal (valuationOf q) (-79)) (literal (valuationOf q) (1039)) (countLit q [-79]) (countLit q [-81]) (count1039 q) 1 (meaningNeg79 q) (meaning1039 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1039 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1039 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 81 = true ∨ valuationOf q 1040 = true := by
  have hs : count1039 q = (countLit q [-79]) + (countLit q [-81]) := List.countP_append (p := literal q) (l₁ := [-79]) (l₂ := [-81])
  have hm := merge_two (literal (valuationOf q) (-79)) (literal (valuationOf q) (-81)) (literal (valuationOf q) (1040)) (countLit q [-79]) (countLit q [-81]) (count1039 q) 1 1 (meaningNeg79 q) (meaningNeg81 q) (meaning1040 q) hs
  change (! (valuationOf q 79)) = false ∨ (! (valuationOf q 81)) = false ∨ valuationOf q 1040 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 81 = true ∨ valuation q 1040 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1041 = true := by
  have hs : count1041 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1041)) (countLit q [-85]) (countLit q [-86]) (count1041 q) 1 (meaningNeg86 q) (meaning1041 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1041 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1041 = true := by
  have hs : count1041 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1041)) (countLit q [-85]) (countLit q [-86]) (count1041 q) 1 (meaningNeg85 q) (meaning1041 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1041 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1041 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1042 = true := by
  have hs : count1041 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1042)) (countLit q [-85]) (countLit q [-86]) (count1041 q) 1 1 (meaningNeg85 q) (meaningNeg86 q) (meaning1042 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1042 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 1042 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 1041 = false ∨ valuationOf q 1043 = true := by
  have hs : count1043 q = (countLit q [-79, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -81]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1041)) (literal (valuationOf q) (1043)) (countLit q [-79, -81]) (countLit q [-85, -86]) (count1043 q) 1 (meaning1041 q) (meaning1043 q) hs
  change valuationOf q 1041 = false ∨ valuationOf q 1043 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 1041 = false ∨ valuation q 1043 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 1042 = false ∨ valuationOf q 1044 = true := by
  have hs : count1043 q = (countLit q [-79, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -81]) (l₂ := [-85, -86])
  have hm := merge_right (literal (valuationOf q) (1042)) (literal (valuationOf q) (1044)) (countLit q [-79, -81]) (countLit q [-85, -86]) (count1043 q) 2 (meaning1042 q) (meaning1044 q) hs
  change valuationOf q 1042 = false ∨ valuationOf q 1044 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 1042 = false ∨ valuation q 1044 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1043 = true := by
  have hs : count1043 q = (countLit q [-79, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -81]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (1039)) (literal (valuationOf q) (1043)) (countLit q [-79, -81]) (countLit q [-85, -86]) (count1043 q) 1 (meaning1039 q) (meaning1043 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1043 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1043 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1044 = true := by
  have hs : count1043 q = (countLit q [-79, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1041)) (literal (valuationOf q) (1044)) (countLit q [-79, -81]) (countLit q [-85, -86]) (count1043 q) 1 1 (meaning1039 q) (meaning1041 q) (meaning1044 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1044 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1041 = false ∨ valuation q 1044 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 1039 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1045 = true := by
  have hs : count1043 q = (countLit q [-79, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1039)) (literal (valuationOf q) (1042)) (literal (valuationOf q) (1045)) (countLit q [-79, -81]) (countLit q [-85, -86]) (count1043 q) 1 2 (meaning1039 q) (meaning1042 q) (meaning1045 q) hs
  change valuationOf q 1039 = false ∨ valuationOf q 1042 = false ∨ valuationOf q 1045 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 1039 = false ∨ valuation q 1042 = false ∨ valuation q 1045 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1044 = true := by
  have hs : count1043 q = (countLit q [-79, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -81]) (l₂ := [-85, -86])
  have hm := merge_left (literal (valuationOf q) (1040)) (literal (valuationOf q) (1044)) (countLit q [-79, -81]) (countLit q [-85, -86]) (count1043 q) 2 (meaning1040 q) (meaning1044 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1044 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1044 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 1040 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1045 = true := by
  have hs : count1043 q = (countLit q [-79, -81]) + (countLit q [-85, -86]) := List.countP_append (p := literal q) (l₁ := [-79, -81]) (l₂ := [-85, -86])
  have hm := merge_two (literal (valuationOf q) (1040)) (literal (valuationOf q) (1041)) (literal (valuationOf q) (1045)) (countLit q [-79, -81]) (countLit q [-85, -86]) (count1043 q) 2 1 (meaning1040 q) (meaning1041 q) (meaning1045 q) hs
  change valuationOf q 1040 = false ∨ valuationOf q 1041 = false ∨ valuationOf q 1045 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 1040 = false ∨ valuation q 1041 = false ∨ valuation q 1045 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_right (literal (valuationOf q) (-89)) (literal (valuationOf q) (1047)) (countLit q [-88]) (countLit q [-89]) (count1047 q) 1 (meaningNeg89 q) (meaning1047 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1047 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1047 = true := by
  have hs : count1047 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1047)) (countLit q [-88]) (countLit q [-89]) (count1047 q) 1 (meaningNeg88 q) (meaning1047 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1047 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1047 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 89 = true ∨ valuationOf q 1048 = true := by
  have hs : count1047 q = (countLit q [-88]) + (countLit q [-89]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (-89)) (literal (valuationOf q) (1048)) (countLit q [-88]) (countLit q [-89]) (count1047 q) 1 1 (meaningNeg88 q) (meaningNeg89 q) (meaning1048 q) hs
  change (! (valuationOf q 88)) = false ∨ (! (valuationOf q 89)) = false ∨ valuationOf q 1048 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 89 = true ∨ valuation q 1048 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1049 = true := by
  have hs : count1049 q = (countLit q [-90]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93])
  have hm := merge_right (literal (valuationOf q) (-93)) (literal (valuationOf q) (1049)) (countLit q [-90]) (countLit q [-93]) (count1049 q) 1 (meaningNeg93 q) (meaning1049 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1049 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E121.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112121
