import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1460 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_left (literal (valuationOf q) (1449)) (literal (valuationOf q) (1460)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 3 (meaning1449 q) (meaning1460 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1460 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1461 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1461)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 3 1 (meaning1449 q) (meaning1454 q) (meaning1461 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1454 = false ∨ valuation q 1461 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1462 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1462)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 3 2 (meaning1449 q) (meaning1455 q) (meaning1462 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1455 = false ∨ valuation q 1462 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1463 = true := by
  have hs : count1458 q = (countLit q [-3, -5, -7]) + (countLit q [-11, -12, -14, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7]) (l₂ := [-11, -12, -14, -17])
  have hm := merge_two (literal (valuationOf q) (1449)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1463)) (countLit q [-3, -5, -7]) (countLit q [-11, -12, -14, -17]) (count1458 q) 3 3 (meaning1449 q) (meaning1456 q) (meaning1463 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1456 = false ∨ valuation q 1463 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_right (literal (valuationOf q) (-23)) (literal (valuationOf q) (1465)) (countLit q [-21]) (countLit q [-23]) (count1465 q) 1 (meaningNeg23 q) (meaning1465 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1465 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1465)) (countLit q [-21]) (countLit q [-23]) (count1465 q) 1 (meaningNeg21 q) (meaning1465 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1465 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1466)) (countLit q [-21]) (countLit q [-23]) (count1465 q) 1 1 (meaningNeg21 q) (meaningNeg23 q) (meaning1466 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 1466 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-20]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21, -23])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1467)) (countLit q [-20]) (countLit q [-21, -23]) (count1467 q) 1 (meaning1465 q) (meaning1467 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1467 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-20]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21, -23])
  have hm := merge_right (literal (valuationOf q) (1466)) (literal (valuationOf q) (1468)) (countLit q [-20]) (countLit q [-21, -23]) (count1467 q) 2 (meaning1466 q) (meaning1468 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1468 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1467 = true := by
  have hs : count1467 q = (countLit q [-20]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21, -23])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1467)) (countLit q [-20]) (countLit q [-21, -23]) (count1467 q) 1 (meaningNeg20 q) (meaning1467 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1467 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true := by
  have hs : count1467 q = (countLit q [-20]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21, -23])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1468)) (countLit q [-20]) (countLit q [-21, -23]) (count1467 q) 1 1 (meaningNeg20 q) (meaning1465 q) (meaning1468 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1465 = false ∨ valuation q 1468 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1466 = false ∨ valuationOf q 1469 = true := by
  have hs : count1467 q = (countLit q [-20]) + (countLit q [-21, -23]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21, -23])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1469)) (countLit q [-20]) (countLit q [-21, -23]) (count1467 q) 1 2 (meaningNeg20 q) (meaning1466 q) (meaning1469 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1466 = false ∨ valuation q 1469 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1470)) (countLit q [-25]) (countLit q [-26]) (count1470 q) 1 (meaningNeg26 q) (meaning1470 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1470 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-25)) (literal (valuationOf q) (1470)) (countLit q [-25]) (countLit q [-26]) (count1470 q) 1 (meaningNeg25 q) (meaning1470 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1470 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-25]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-25]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-25)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1471)) (countLit q [-25]) (countLit q [-26]) (count1470 q) 1 1 (meaningNeg25 q) (meaningNeg26 q) (meaning1471 q) hs
  change (! (valuationOf q 25)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 26 = true ∨ valuation q 1471 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (1472)) (countLit q [-28]) (countLit q [-31]) (count1472 q) 1 (meaningNeg31 q) (meaning1472 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 1472 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1472 = true := by
  have hs : count1472 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1472)) (countLit q [-28]) (countLit q [-31]) (count1472 q) 1 (meaningNeg28 q) (meaning1472 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1472 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 31 = true ∨ valuationOf q 1473 = true := by
  have hs : count1472 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (1473)) (countLit q [-28]) (countLit q [-31]) (count1472 q) 1 1 (meaningNeg28 q) (meaningNeg31 q) (meaning1473 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 1473 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-25, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -26]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-25, -26]) (countLit q [-28, -31]) (count1474 q) 1 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-25, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -26]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (1473)) (literal (valuationOf q) (1475)) (countLit q [-25, -26]) (countLit q [-28, -31]) (count1474 q) 2 (meaning1473 q) (meaning1475 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1475 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1474 = true := by
  have hs : count1474 q = (countLit q [-25, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -26]) (l₂ := [-28, -31])
  have hm := merge_left (literal (valuationOf q) (1470)) (literal (valuationOf q) (1474)) (countLit q [-25, -26]) (countLit q [-28, -31]) (count1474 q) 1 (meaning1470 q) (meaning1474 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1474 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-25, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -26]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (countLit q [-25, -26]) (countLit q [-28, -31]) (count1474 q) 1 1 (meaning1470 q) (meaning1472 q) (meaning1475 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1472 = false ∨ valuation q 1475 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1470 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true := by
  have hs : count1474 q = (countLit q [-25, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -26]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1470)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1476)) (countLit q [-25, -26]) (countLit q [-28, -31]) (count1474 q) 1 2 (meaning1470 q) (meaning1473 q) (meaning1476 q) hs
  change valuationOf q 1470 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1470 = false ∨ valuation q 1473 = false ∨ valuation q 1476 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1475 = true := by
  have hs : count1474 q = (countLit q [-25, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -26]) (l₂ := [-28, -31])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1475)) (countLit q [-25, -26]) (countLit q [-28, -31]) (count1474 q) 2 (meaning1471 q) (meaning1475 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1475 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1476 = true := by
  have hs : count1474 q = (countLit q [-25, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -26]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1476)) (countLit q [-25, -26]) (countLit q [-28, -31]) (count1474 q) 2 1 (meaning1471 q) (meaning1472 q) (meaning1476 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1476 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1472 = false ∨ valuation q 1476 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1477 = true := by
  have hs : count1474 q = (countLit q [-25, -26]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-25, -26]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (literal (valuationOf q) (1477)) (countLit q [-25, -26]) (countLit q [-28, -31]) (count1474 q) 2 2 (meaning1471 q) (meaning1473 q) (meaning1477 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = false ∨ valuationOf q 1477 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = false ∨ valuation q 1477 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1474)) (literal (valuationOf q) (1478)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 1 (meaning1474 q) (meaning1478 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1478 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1475)) (literal (valuationOf q) (1479)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 2 (meaning1475 q) (meaning1479 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1479 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1476 = false ∨ valuationOf q 1480 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1476)) (literal (valuationOf q) (1480)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 3 (meaning1476 q) (meaning1480 q) hs
  change valuationOf q 1476 = false ∨ valuationOf q 1480 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1476 = false ∨ valuation q 1480 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1477 = false ∨ valuationOf q 1481 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_right (literal (valuationOf q) (1477)) (literal (valuationOf q) (1481)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 4 (meaning1477 q) (meaning1481 q) hs
  change valuationOf q 1477 = false ∨ valuationOf q 1481 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1477 = false ∨ valuation q 1481 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1478 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_left (literal (valuationOf q) (1467)) (literal (valuationOf q) (1478)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 1 (meaning1467 q) (meaning1478 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1478 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1478 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true := by
  have hs : count1478 q = (countLit q [-20, -21, -23]) + (countLit q [-25, -26, -28, -31]) := List.countP_append (p := literal q) (l₁ := [-20, -21, -23]) (l₂ := [-25, -26, -28, -31])
  have hm := merge_two (literal (valuationOf q) (1467)) (literal (valuationOf q) (1474)) (literal (valuationOf q) (1479)) (countLit q [-20, -21, -23]) (countLit q [-25, -26, -28, -31]) (count1478 q) 1 1 (meaning1467 q) (meaning1474 q) (meaning1479 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1474 = false ∨ valuationOf q 1479 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1474 = false ∨ valuation q 1479 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E047.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112047
