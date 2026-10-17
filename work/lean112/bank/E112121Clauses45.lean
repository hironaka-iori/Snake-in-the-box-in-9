import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1049 = true := by
  have hs : count1049 q = (countLit q [-90]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93])
  have hm := merge_left (literal (valuationOf q) (-90)) (literal (valuationOf q) (1049)) (countLit q [-90]) (countLit q [-93]) (count1049 q) 1 (meaningNeg90 q) (meaning1049 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1049 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1049 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 93 = true ∨ valuationOf q 1050 = true := by
  have hs : count1049 q = (countLit q [-90]) + (countLit q [-93]) := List.countP_append (p := literal q) (l₁ := [-90]) (l₂ := [-93])
  have hm := merge_two (literal (valuationOf q) (-90)) (literal (valuationOf q) (-93)) (literal (valuationOf q) (1050)) (countLit q [-90]) (countLit q [-93]) (count1049 q) 1 1 (meaningNeg90 q) (meaningNeg93 q) (meaning1050 q) hs
  change (! (valuationOf q 90)) = false ∨ (! (valuationOf q 93)) = false ∨ valuationOf q 1050 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 93 = true ∨ valuation q 1050 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 1049 = false ∨ valuationOf q 1051 = true := by
  have hs : count1051 q = (countLit q [-88, -89]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-90, -93])
  have hm := merge_right (literal (valuationOf q) (1049)) (literal (valuationOf q) (1051)) (countLit q [-88, -89]) (countLit q [-90, -93]) (count1051 q) 1 (meaning1049 q) (meaning1051 q) hs
  change valuationOf q 1049 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 1049 = false ∨ valuation q 1051 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 1050 = false ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-88, -89]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-90, -93])
  have hm := merge_right (literal (valuationOf q) (1050)) (literal (valuationOf q) (1052)) (countLit q [-88, -89]) (countLit q [-90, -93]) (count1051 q) 2 (meaning1050 q) (meaning1052 q) hs
  change valuationOf q 1050 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 1050 = false ∨ valuation q 1052 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1051 = true := by
  have hs : count1051 q = (countLit q [-88, -89]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-90, -93])
  have hm := merge_left (literal (valuationOf q) (1047)) (literal (valuationOf q) (1051)) (countLit q [-88, -89]) (countLit q [-90, -93]) (count1051 q) 1 (meaning1047 q) (meaning1051 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1051 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1051 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-88, -89]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-90, -93])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1049)) (literal (valuationOf q) (1052)) (countLit q [-88, -89]) (countLit q [-90, -93]) (count1051 q) 1 1 (meaning1047 q) (meaning1049 q) (meaning1052 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1049 = false ∨ valuation q 1052 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 1047 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1053 = true := by
  have hs : count1051 q = (countLit q [-88, -89]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-90, -93])
  have hm := merge_two (literal (valuationOf q) (1047)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1053)) (countLit q [-88, -89]) (countLit q [-90, -93]) (count1051 q) 1 2 (meaning1047 q) (meaning1050 q) (meaning1053 q) hs
  change valuationOf q 1047 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 1047 = false ∨ valuation q 1050 = false ∨ valuation q 1053 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1052 = true := by
  have hs : count1051 q = (countLit q [-88, -89]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-90, -93])
  have hm := merge_left (literal (valuationOf q) (1048)) (literal (valuationOf q) (1052)) (countLit q [-88, -89]) (countLit q [-90, -93]) (count1051 q) 2 (meaning1048 q) (meaning1052 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1052 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1052 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1053 = true := by
  have hs : count1051 q = (countLit q [-88, -89]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-90, -93])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1049)) (literal (valuationOf q) (1053)) (countLit q [-88, -89]) (countLit q [-90, -93]) (count1051 q) 2 1 (meaning1048 q) (meaning1049 q) (meaning1053 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1049 = false ∨ valuationOf q 1053 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1049 = false ∨ valuation q 1053 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 1048 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1054 = true := by
  have hs : count1051 q = (countLit q [-88, -89]) + (countLit q [-90, -93]) := List.countP_append (p := literal q) (l₁ := [-88, -89]) (l₂ := [-90, -93])
  have hm := merge_two (literal (valuationOf q) (1048)) (literal (valuationOf q) (1050)) (literal (valuationOf q) (1054)) (countLit q [-88, -89]) (countLit q [-90, -93]) (count1051 q) 2 2 (meaning1048 q) (meaning1050 q) (meaning1054 q) hs
  change valuationOf q 1048 = false ∨ valuationOf q 1050 = false ∨ valuationOf q 1054 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 1048 = false ∨ valuation q 1050 = false ∨ valuation q 1054 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 1051 = false ∨ valuationOf q 1055 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1051)) (literal (valuationOf q) (1055)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 1 (meaning1051 q) (meaning1055 q) hs
  change valuationOf q 1051 = false ∨ valuationOf q 1055 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 1051 = false ∨ valuation q 1055 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 1053 = false ∨ valuationOf q 1057 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1053)) (literal (valuationOf q) (1057)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 3 (meaning1053 q) (meaning1057 q) hs
  change valuationOf q 1053 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 1053 = false ∨ valuation q 1057 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 1054 = false ∨ valuationOf q 1058 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1054)) (literal (valuationOf q) (1058)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 4 (meaning1054 q) (meaning1058 q) hs
  change valuationOf q 1054 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 1054 = false ∨ valuation q 1058 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 1043 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1056 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1043)) (literal (valuationOf q) (1051)) (literal (valuationOf q) (1056)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 1 1 (meaning1043 q) (meaning1051 q) (meaning1056 q) hs
  change valuationOf q 1043 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1056 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 1043 = false ∨ valuation q 1051 = false ∨ valuation q 1056 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 1043 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1057 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1043)) (literal (valuationOf q) (1052)) (literal (valuationOf q) (1057)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 1 2 (meaning1043 q) (meaning1052 q) (meaning1057 q) hs
  change valuationOf q 1043 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 1043 = false ∨ valuation q 1052 = false ∨ valuation q 1057 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 1043 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1058 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1043)) (literal (valuationOf q) (1053)) (literal (valuationOf q) (1058)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 1 3 (meaning1043 q) (meaning1053 q) (meaning1058 q) hs
  change valuationOf q 1043 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 1043 = false ∨ valuation q 1053 = false ∨ valuation q 1058 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 1043 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1059 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1043)) (literal (valuationOf q) (1054)) (literal (valuationOf q) (1059)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 1 4 (meaning1043 q) (meaning1054 q) (meaning1059 q) hs
  change valuationOf q 1043 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 1043 = false ∨ valuation q 1054 = false ∨ valuation q 1059 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 1044 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1057 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1044)) (literal (valuationOf q) (1051)) (literal (valuationOf q) (1057)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 2 1 (meaning1044 q) (meaning1051 q) (meaning1057 q) hs
  change valuationOf q 1044 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1057 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 1044 = false ∨ valuation q 1051 = false ∨ valuation q 1057 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 1044 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1058 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1044)) (literal (valuationOf q) (1052)) (literal (valuationOf q) (1058)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 2 2 (meaning1044 q) (meaning1052 q) (meaning1058 q) hs
  change valuationOf q 1044 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 1044 = false ∨ valuation q 1052 = false ∨ valuation q 1058 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 1044 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1059 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1044)) (literal (valuationOf q) (1053)) (literal (valuationOf q) (1059)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 2 3 (meaning1044 q) (meaning1053 q) (meaning1059 q) hs
  change valuationOf q 1044 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 1044 = false ∨ valuation q 1053 = false ∨ valuation q 1059 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 1044 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1060 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1044)) (literal (valuationOf q) (1054)) (literal (valuationOf q) (1060)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 2 4 (meaning1044 q) (meaning1054 q) (meaning1060 q) hs
  change valuationOf q 1044 = false ∨ valuationOf q 1054 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 1044 = false ∨ valuation q 1054 = false ∨ valuation q 1060 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 1045 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1058 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1045)) (literal (valuationOf q) (1051)) (literal (valuationOf q) (1058)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 3 1 (meaning1045 q) (meaning1051 q) (meaning1058 q) hs
  change valuationOf q 1045 = false ∨ valuationOf q 1051 = false ∨ valuationOf q 1058 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 1045 = false ∨ valuation q 1051 = false ∨ valuation q 1058 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 1045 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1059 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1045)) (literal (valuationOf q) (1052)) (literal (valuationOf q) (1059)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 3 2 (meaning1045 q) (meaning1052 q) (meaning1059 q) hs
  change valuationOf q 1045 = false ∨ valuationOf q 1052 = false ∨ valuationOf q 1059 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 1045 = false ∨ valuation q 1052 = false ∨ valuation q 1059 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 1045 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1060 = true := by
  have hs : count1055 q = (countLit q [-79, -81, -85, -86]) + (countLit q [-88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-79, -81, -85, -86]) (l₂ := [-88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1045)) (literal (valuationOf q) (1053)) (literal (valuationOf q) (1060)) (countLit q [-79, -81, -85, -86]) (countLit q [-88, -89, -90, -93]) (count1055 q) 3 3 (meaning1045 q) (meaning1053 q) (meaning1060 q) hs
  change valuationOf q 1045 = false ∨ valuationOf q 1053 = false ∨ valuationOf q 1060 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 1045 = false ∨ valuation q 1053 = false ∨ valuation q 1060 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 1055 = false ∨ valuationOf q 1063 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1055)) (literal (valuationOf q) (1063)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 1 (meaning1055 q) (meaning1063 q) hs
  change valuationOf q 1055 = false ∨ valuationOf q 1063 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 1055 = false ∨ valuation q 1063 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 1056 = false ∨ valuationOf q 1064 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1056)) (literal (valuationOf q) (1064)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 2 (meaning1056 q) (meaning1064 q) hs
  change valuationOf q 1056 = false ∨ valuationOf q 1064 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 1056 = false ∨ valuation q 1064 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 1057 = false ∨ valuationOf q 1065 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1057)) (literal (valuationOf q) (1065)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 3 (meaning1057 q) (meaning1065 q) hs
  change valuationOf q 1057 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 1057 = false ∨ valuation q 1065 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 1058 = false ∨ valuationOf q 1066 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1058)) (literal (valuationOf q) (1066)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 4 (meaning1058 q) (meaning1066 q) hs
  change valuationOf q 1058 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 1058 = false ∨ valuation q 1066 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 1059 = false ∨ valuationOf q 1067 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1059)) (literal (valuationOf q) (1067)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 5 (meaning1059 q) (meaning1067 q) hs
  change valuationOf q 1059 = false ∨ valuationOf q 1067 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 1059 = false ∨ valuation q 1067 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 1060 = false ∨ valuationOf q 1068 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_right (literal (valuationOf q) (1060)) (literal (valuationOf q) (1068)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 6 (meaning1060 q) (meaning1068 q) hs
  change valuationOf q 1060 = false ∨ valuationOf q 1068 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 1060 = false ∨ valuation q 1068 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 1031 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1065 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1031)) (literal (valuationOf q) (1056)) (literal (valuationOf q) (1065)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 1 2 (meaning1031 q) (meaning1056 q) (meaning1065 q) hs
  change valuationOf q 1031 = false ∨ valuationOf q 1056 = false ∨ valuationOf q 1065 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 1031 = false ∨ valuation q 1056 = false ∨ valuation q 1065 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 1031 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1066 = true := by
  have hs : count1063 q = (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) + (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) := List.countP_append (p := literal q) (l₁ := [-63, -66, -68, -69, -71, -74, -77, -78]) (l₂ := [-79, -81, -85, -86, -88, -89, -90, -93])
  have hm := merge_two (literal (valuationOf q) (1031)) (literal (valuationOf q) (1057)) (literal (valuationOf q) (1066)) (countLit q [-63, -66, -68, -69, -71, -74, -77, -78]) (countLit q [-79, -81, -85, -86, -88, -89, -90, -93]) (count1063 q) 1 3 (meaning1031 q) (meaning1057 q) (meaning1066 q) hs
  change valuationOf q 1031 = false ∨ valuationOf q 1057 = false ∨ valuationOf q 1066 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 1031 = false ∨ valuation q 1057 = false ∨ valuation q 1066 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E121.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112121
