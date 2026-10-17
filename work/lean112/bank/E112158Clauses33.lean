import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1451)) (literal (valuationOf q) (1455)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 2 (meaning1451 q) (meaning1455 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1455 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 3 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1457)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 4 (meaning1453 q) (meaning1457 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1457 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1443)) (literal (valuationOf q) (1454)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 1 (meaning1443 q) (meaning1454 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1454 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1455)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 1 1 (meaning1443 q) (meaning1450 q) (meaning1455 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1450 = false ∨ valuation q 1455 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1456)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 1 2 (meaning1443 q) (meaning1451 q) (meaning1456 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1451 = false ∨ valuation q 1456 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1457)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 1 3 (meaning1443 q) (meaning1452 q) (meaning1457 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1452 = false ∨ valuation q 1457 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1458)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 1 4 (meaning1443 q) (meaning1453 q) (meaning1458 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1453 = false ∨ valuation q 1458 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1444)) (literal (valuationOf q) (1455)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 2 (meaning1444 q) (meaning1455 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1455 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1456)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 2 1 (meaning1444 q) (meaning1450 q) (meaning1456 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1450 = false ∨ valuation q 1456 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1457)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 2 2 (meaning1444 q) (meaning1451 q) (meaning1457 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1451 = false ∨ valuation q 1457 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1458)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 2 3 (meaning1444 q) (meaning1452 q) (meaning1458 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1452 = false ∨ valuation q 1458 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_left (literal (valuationOf q) (1445)) (literal (valuationOf q) (1456)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 3 (meaning1445 q) (meaning1456 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1456 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1457)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 3 1 (meaning1445 q) (meaning1450 q) (meaning1457 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1450 = false ∨ valuation q 1457 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1458 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1458)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 3 2 (meaning1445 q) (meaning1451 q) (meaning1458 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1451 = false ∨ valuation q 1458 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1459 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1459)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 3 3 (meaning1445 q) (meaning1452 q) (meaning1459 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1452 = false ∨ valuation q 1459 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1460 = true := by
  have hs : count1454 q = (countLit q [-19, -20, -21]) + (countLit q [-24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-19, -20, -21]) (l₂ := [-24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1460)) (countLit q [-19, -20, -21]) (countLit q [-24, -25, -28, -30]) (count1454 q) 3 4 (meaning1445 q) (meaning1453 q) (meaning1460 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1453 = false ∨ valuation q 1460 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1454 = false ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1454)) (literal (valuationOf q) (1461)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 1 (meaning1454 q) (meaning1461 q) hs
  change valuationOf q 1454 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1454 = false ∨ valuation q 1461 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1455 = false ∨ valuationOf q 1462 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1455)) (literal (valuationOf q) (1462)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 2 (meaning1455 q) (meaning1462 q) hs
  change valuationOf q 1455 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1455 = false ∨ valuation q 1462 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1456 = false ∨ valuationOf q 1463 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1456)) (literal (valuationOf q) (1463)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 3 (meaning1456 q) (meaning1463 q) hs
  change valuationOf q 1456 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1456 = false ∨ valuation q 1463 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1464 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1457)) (literal (valuationOf q) (1464)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 4 (meaning1457 q) (meaning1464 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1464 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1465 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1458)) (literal (valuationOf q) (1465)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 5 (meaning1458 q) (meaning1465 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1465 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1466 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1459)) (literal (valuationOf q) (1466)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 6 (meaning1459 q) (meaning1466 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1466 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1467 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_right (literal (valuationOf q) (1460)) (literal (valuationOf q) (1467)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 7 (meaning1460 q) (meaning1467 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1467 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1462 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1462)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 1 1 (meaning1434 q) (meaning1454 q) (meaning1462 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1454 = false ∨ valuation q 1462 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1463 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1463)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 1 2 (meaning1434 q) (meaning1455 q) (meaning1463 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1455 = false ∨ valuation q 1463 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1464 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1464)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 1 3 (meaning1434 q) (meaning1456 q) (meaning1464 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1456 = false ∨ valuation q 1464 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1465 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1465)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 1 4 (meaning1434 q) (meaning1457 q) (meaning1465 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1457 = false ∨ valuation q 1465 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1466 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1466)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 1 5 (meaning1434 q) (meaning1458 q) (meaning1466 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1458 = false ∨ valuation q 1466 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1467 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1434)) (literal (valuationOf q) (1459)) (literal (valuationOf q) (1467)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 1 6 (meaning1434 q) (meaning1459 q) (meaning1467 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1459 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1459 = false ∨ valuation q 1467 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1463 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1463)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 2 1 (meaning1435 q) (meaning1454 q) (meaning1463 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1454 = false ∨ valuation q 1463 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1435 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1464 = true := by
  have hs : count1461 q = (countLit q [-3, -6, -7, -9, -11, -13, -17]) + (countLit q [-19, -20, -21, -24, -25, -28, -30]) := List.countP_append (p := literal q) (l₁ := [-3, -6, -7, -9, -11, -13, -17]) (l₂ := [-19, -20, -21, -24, -25, -28, -30])
  have hm := merge_two (literal (valuationOf q) (1435)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1464)) (countLit q [-3, -6, -7, -9, -11, -13, -17]) (countLit q [-19, -20, -21, -24, -25, -28, -30]) (count1461 q) 2 2 (meaning1435 q) (meaning1455 q) (meaning1464 q) hs
  change valuationOf q 1435 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1435 = false ∨ valuation q 1455 = false ∨ valuation q 1464 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E158.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112158
