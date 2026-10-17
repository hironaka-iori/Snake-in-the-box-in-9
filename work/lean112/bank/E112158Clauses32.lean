import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1436)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 1 2 (meaning1423 q) (meaning1431 q) (meaning1436 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1431 = false ∨ valuation q 1436 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1437)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 1 3 (meaning1423 q) (meaning1432 q) (meaning1437 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1432 = false ∨ valuation q 1437 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1438 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_two (literal (valuationOf q) (1423)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1438)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 1 4 (meaning1423 q) (meaning1433 q) (meaning1438 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1433 = false ∨ valuation q 1438 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_left (literal (valuationOf q) (1424)) (literal (valuationOf q) (1435)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 2 (meaning1424 q) (meaning1435 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1435 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1430)) (literal (valuationOf q) (1436)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 2 1 (meaning1424 q) (meaning1430 q) (meaning1436 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1430 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1430 = false ∨ valuation q 1436 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1437 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1437)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 2 2 (meaning1424 q) (meaning1431 q) (meaning1437 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1437 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1431 = false ∨ valuation q 1437 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1438 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_two (literal (valuationOf q) (1424)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1438)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 2 3 (meaning1424 q) (meaning1432 q) (meaning1438 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1432 = false ∨ valuation q 1438 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_left (literal (valuationOf q) (1425)) (literal (valuationOf q) (1436)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 3 (meaning1425 q) (meaning1436 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1436 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1425 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1438 = true := by
  have hs : count1434 q = (countLit q [-3, -6, -7]) + (countLit q [-9, -11, -13, -17]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7]) (l₂ := [-9, -11, -13, -17])
  have hm := merge_two (literal (valuationOf q) (1425)) (literal (valuationOf q) (1431)) (literal (valuationOf q) (1438)) (countLit q [-3, -6, -7]) (countLit q [-9, -11, -13, -17]) (count1434 q) 3 2 (meaning1425 q) (meaning1431 q) (meaning1438 q) hs
  change valuationOf q 1425 = false ∨ valuationOf q 1431 = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1425 = false ∨ valuation q 1431 = false ∨ valuation q 1438 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (1441)) (countLit q [-20]) (countLit q [-21]) (count1441 q) 1 (meaningNeg21 q) (meaning1441 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1441 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1441)) (countLit q [-20]) (countLit q [-21]) (count1441 q) 1 (meaningNeg20 q) (meaning1441 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1441 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 21 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (1442)) (countLit q [-20]) (countLit q [-21]) (count1441 q) 1 1 (meaningNeg20 q) (meaningNeg21 q) (meaning1442 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 1442 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-19]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (countLit q [-19]) (countLit q [-20, -21]) (count1443 q) 1 (meaning1441 q) (meaning1443 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-19]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (1442)) (literal (valuationOf q) (1444)) (countLit q [-19]) (countLit q [-20, -21]) (count1443 q) 2 (meaning1442 q) (meaning1444 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1444 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-19]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20, -21])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1443)) (countLit q [-19]) (countLit q [-20, -21]) (count1443 q) 1 (meaningNeg19 q) (meaning1443 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1443 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-19]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1444)) (countLit q [-19]) (countLit q [-20, -21]) (count1443 q) 1 1 (meaningNeg19 q) (meaning1441 q) (meaning1444 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1441 = false ∨ valuation q 1444 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1442 = false ∨ valuationOf q 1445 = true := by
  have hs : count1443 q = (countLit q [-19]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1445)) (countLit q [-19]) (countLit q [-20, -21]) (count1443 q) 1 2 (meaningNeg19 q) (meaning1442 q) (meaning1445 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1442 = false ∨ valuation q 1445 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (1446)) (countLit q [-24]) (countLit q [-25]) (count1446 q) 1 (meaningNeg25 q) (meaning1446 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 1446 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1446)) (countLit q [-24]) (countLit q [-25]) (count1446 q) 1 (meaningNeg24 q) (meaning1446 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1446 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (1447)) (countLit q [-24]) (countLit q [-25]) (count1446 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning1447 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 1447 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1448)) (countLit q [-28]) (countLit q [-30]) (count1448 q) 1 (meaningNeg30 q) (meaning1448 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1448 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1448)) (countLit q [-28]) (countLit q [-30]) (count1448 q) 1 (meaningNeg28 q) (meaning1448 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1448 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1449)) (countLit q [-28]) (countLit q [-30]) (count1448 q) 1 1 (meaningNeg28 q) (meaningNeg30 q) (meaning1449 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 30 = true ∨ valuation q 1449 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1450)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1450 q) 1 (meaning1448 q) (meaning1450 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1450 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1451)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1450 q) 2 (meaning1449 q) (meaning1451 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1451 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (1446)) (literal (valuationOf q) (1450)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1450 q) 1 (meaning1446 q) (meaning1450 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1450 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1450 q) 1 1 (meaning1446 q) (meaning1448 q) (meaning1451 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = false ∨ valuation q 1451 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1452)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1450 q) 1 2 (meaning1446 q) (meaning1449 q) (meaning1452 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1449 = false ∨ valuation q 1452 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (1447)) (literal (valuationOf q) (1451)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1450 q) 2 (meaning1447 q) (meaning1451 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1451 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1450 q) 2 1 (meaning1447 q) (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1448 = false ∨ valuation q 1452 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1450 q = (countLit q [-24, -25]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -25]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-24, -25]) (countLit q [-28, -30]) (count1450 q) 2 2 (meaning1447 q) (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = false ∨ valuation q 1453 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 1 (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1454 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E158.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112158
