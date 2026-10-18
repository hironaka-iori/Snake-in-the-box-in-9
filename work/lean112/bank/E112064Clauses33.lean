import E112064Semantics
import B112E064Inputs
namespace Snake9.Regrowth.E112064
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1482 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1497 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1482)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1497)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 2 3 (meaning1482 q) (meaning1491 q) (meaning1497 q) hs
  change valuationOf q 1482 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1482 = false ∨ valuation q 1491 = false ∨ valuation q 1497 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1495 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_left (literal (valuationOf q) (1483)) (literal (valuationOf q) (1495)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 3 (meaning1483 q) (meaning1495 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1495 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1495 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1496 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1496)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 3 1 (meaning1483 q) (meaning1489 q) (meaning1496 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1489 = false ∨ valuation q 1496 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1497 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1490)) (literal (valuationOf q) (1497)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 3 2 (meaning1483 q) (meaning1490 q) (meaning1497 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1490 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1490 = false ∨ valuation q 1497 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1483 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1498 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1483)) (literal (valuationOf q) (1491)) (literal (valuationOf q) (1498)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 3 3 (meaning1483 q) (meaning1491 q) (meaning1498 q) hs
  change valuationOf q 1483 = false ∨ valuationOf q 1491 = false ∨ valuationOf q 1498 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1483 = false ∨ valuation q 1491 = false ∨ valuation q 1498 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1496 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_left (literal (valuationOf q) (1484)) (literal (valuationOf q) (1496)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 4 (meaning1484 q) (meaning1496 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1496 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1496 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1484 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1497 = true := by
  have hs : count1493 q = (countLit q [-43, -44, -46, -49]) + (countLit q [-50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-43, -44, -46, -49]) (l₂ := [-50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1484)) (literal (valuationOf q) (1489)) (literal (valuationOf q) (1497)) (countLit q [-43, -44, -46, -49]) (countLit q [-50, -51, -52, -56]) (count1493 q) 4 1 (meaning1484 q) (meaning1489 q) (meaning1497 q) hs
  change valuationOf q 1484 = false ∨ valuationOf q 1489 = false ∨ valuationOf q 1497 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1484 = false ∨ valuation q 1489 = false ∨ valuation q 1497 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1502 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_left (literal (valuationOf q) (1471)) (literal (valuationOf q) (1502)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 2 (meaning1471 q) (meaning1502 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1502 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1503 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1503)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 2 1 (meaning1471 q) (meaning1493 q) (meaning1503 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1493 = false ∨ valuation q 1503 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1504 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1504)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 2 2 (meaning1471 q) (meaning1494 q) (meaning1504 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1494 = false ∨ valuation q 1504 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1505 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1505)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 2 3 (meaning1471 q) (meaning1495 q) (meaning1505 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1495 = false ∨ valuation q 1505 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1506 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1506)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 2 4 (meaning1471 q) (meaning1496 q) (meaning1506 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1496 = false ∨ valuation q 1506 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1507 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1507)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 2 5 (meaning1471 q) (meaning1497 q) (meaning1507 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1497 = false ∨ valuation q 1507 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1508 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1471)) (literal (valuationOf q) (1498)) (literal (valuationOf q) (1508)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 2 6 (meaning1471 q) (meaning1498 q) (meaning1508 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1498 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1498 = false ∨ valuation q 1508 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1503 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_left (literal (valuationOf q) (1472)) (literal (valuationOf q) (1503)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 3 (meaning1472 q) (meaning1503 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1503 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1504 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1504)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 3 1 (meaning1472 q) (meaning1493 q) (meaning1504 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1493 = false ∨ valuation q 1504 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1505 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1505)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 3 2 (meaning1472 q) (meaning1494 q) (meaning1505 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1494 = false ∨ valuation q 1505 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1506 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1506)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 3 3 (meaning1472 q) (meaning1495 q) (meaning1506 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1495 = false ∨ valuation q 1506 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1507 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1507)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 3 4 (meaning1472 q) (meaning1496 q) (meaning1507 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1496 = false ∨ valuation q 1507 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1508 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1472)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1508)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 3 5 (meaning1472 q) (meaning1497 q) (meaning1508 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1497 = false ∨ valuation q 1508 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1504 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_left (literal (valuationOf q) (1473)) (literal (valuationOf q) (1504)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 4 (meaning1473 q) (meaning1504 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1504 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1505 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1505)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 4 1 (meaning1473 q) (meaning1493 q) (meaning1505 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1493 = false ∨ valuation q 1505 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1506 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1506)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 4 2 (meaning1473 q) (meaning1494 q) (meaning1506 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1494 = false ∨ valuation q 1506 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1507 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1507)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 4 3 (meaning1473 q) (meaning1495 q) (meaning1507 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1495 = false ∨ valuation q 1507 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1508 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1508)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 4 4 (meaning1473 q) (meaning1496 q) (meaning1508 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1496 = false ∨ valuation q 1508 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1473 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1509 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1473)) (literal (valuationOf q) (1497)) (literal (valuationOf q) (1509)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 4 5 (meaning1473 q) (meaning1497 q) (meaning1509 q) hs
  change valuationOf q 1473 = false ∨ valuationOf q 1497 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1473 = false ∨ valuation q 1497 = false ∨ valuation q 1509 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1505 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_left (literal (valuationOf q) (1474)) (literal (valuationOf q) (1505)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 5 (meaning1474 q) (meaning1505 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1505 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1506 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1493)) (literal (valuationOf q) (1506)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 5 1 (meaning1474 q) (meaning1493 q) (meaning1506 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1493 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1493 = false ∨ valuation q 1506 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1507 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1494)) (literal (valuationOf q) (1507)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 5 2 (meaning1474 q) (meaning1494 q) (meaning1507 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1494 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1494 = false ∨ valuation q 1507 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1508 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1495)) (literal (valuationOf q) (1508)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 5 3 (meaning1474 q) (meaning1495 q) (meaning1508 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1495 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1495 = false ∨ valuation q 1508 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1474 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1509 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_two (literal (valuationOf q) (1474)) (literal (valuationOf q) (1496)) (literal (valuationOf q) (1509)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 5 4 (meaning1474 q) (meaning1496 q) (meaning1509 q) hs
  change valuationOf q 1474 = false ∨ valuationOf q 1496 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1474 = false ∨ valuation q 1496 = false ∨ valuation q 1509 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1475 = false ∨ valuationOf q 1506 = true := by
  have hs : count1501 q = (countLit q [-27, -29, -30, -33, -35, -37, -41]) + (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) := List.countP_append (p := literal q) (l₁ := [-27, -29, -30, -33, -35, -37, -41]) (l₂ := [-43, -44, -46, -49, -50, -51, -52, -56])
  have hm := merge_left (literal (valuationOf q) (1475)) (literal (valuationOf q) (1506)) (countLit q [-27, -29, -30, -33, -35, -37, -41]) (countLit q [-43, -44, -46, -49, -50, -51, -52, -56]) (count1501 q) 6 (meaning1475 q) (meaning1506 q) hs
  change valuationOf q 1475 = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1475 = false ∨ valuation q 1506 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E064.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112064
