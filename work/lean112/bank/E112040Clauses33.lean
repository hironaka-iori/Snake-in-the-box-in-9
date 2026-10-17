import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-34, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -37])
  have hm := merge_right (literal (valuationOf q) (1501)) (literal (valuationOf q) (1503)) (countLit q [-32]) (countLit q [-34, -37]) (count1502 q) 2 (meaning1501 q) (meaning1503 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1503 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1502 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-34, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -37])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1502)) (countLit q [-32]) (countLit q [-34, -37]) (count1502 q) 1 (meaningNeg32 q) (meaning1502 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1502 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1502 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1500 = false ∨ valuationOf q 1503 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-34, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -37])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1500)) (literal (valuationOf q) (1503)) (countLit q [-32]) (countLit q [-34, -37]) (count1502 q) 1 1 (meaningNeg32 q) (meaning1500 q) (meaning1503 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1500 = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1500 = false ∨ valuation q 1503 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true := by
  have hs : count1502 q = (countLit q [-32]) + (countLit q [-34, -37]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -37])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1501)) (literal (valuationOf q) (1504)) (countLit q [-32]) (countLit q [-34, -37]) (count1502 q) 1 2 (meaningNeg32 q) (meaning1501 q) (meaning1504 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1501 = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1501 = false ∨ valuation q 1504 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_right (literal (valuationOf q) (-39)) (literal (valuationOf q) (1505)) (countLit q [-38]) (countLit q [-39]) (count1505 q) 1 (meaningNeg39 q) (meaning1505 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 1505 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1505)) (countLit q [-38]) (countLit q [-39]) (count1505 q) 1 (meaningNeg38 q) (meaning1505 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1505 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 39 = true ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-38]) + (countLit q [-39]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-39])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-39)) (literal (valuationOf q) (1506)) (countLit q [-38]) (countLit q [-39]) (count1505 q) 1 1 (meaningNeg38 q) (meaningNeg39 q) (meaning1506 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 39)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 39 = true ∨ valuation q 1506 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (1507)) (countLit q [-42]) (countLit q [-44]) (count1507 q) 1 (meaningNeg44 q) (meaning1507 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1507 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (1507)) (countLit q [-42]) (countLit q [-44]) (count1507 q) 1 (meaningNeg42 q) (meaning1507 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 1507 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 44 = true ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (1508)) (countLit q [-42]) (countLit q [-44]) (count1507 q) 1 1 (meaningNeg42 q) (meaningNeg44 q) (meaning1508 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 44 = true ∨ valuation q 1508 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1509 = true := by
  have hs : count1509 q = (countLit q [-38, -39]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1507)) (literal (valuationOf q) (1509)) (countLit q [-38, -39]) (countLit q [-42, -44]) (count1509 q) 1 (meaning1507 q) (meaning1509 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1509 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1510 = true := by
  have hs : count1509 q = (countLit q [-38, -39]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-42, -44])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1510)) (countLit q [-38, -39]) (countLit q [-42, -44]) (count1509 q) 2 (meaning1508 q) (meaning1510 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1510 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1509 q = (countLit q [-38, -39]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-42, -44])
  have hm := merge_left (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-38, -39]) (countLit q [-42, -44]) (count1509 q) 1 (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1509 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1510 = true := by
  have hs : count1509 q = (countLit q [-38, -39]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1510)) (countLit q [-38, -39]) (countLit q [-42, -44]) (count1509 q) 1 1 (meaning1505 q) (meaning1507 q) (meaning1510 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = false ∨ valuation q 1510 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true := by
  have hs : count1509 q = (countLit q [-38, -39]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1511)) (countLit q [-38, -39]) (countLit q [-42, -44]) (count1509 q) 1 2 (meaning1505 q) (meaning1508 q) (meaning1511 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1508 = false ∨ valuation q 1511 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1509 q = (countLit q [-38, -39]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-42, -44])
  have hm := merge_left (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-38, -39]) (countLit q [-42, -44]) (count1509 q) 2 (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1510 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1509 q = (countLit q [-38, -39]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-38, -39]) (countLit q [-42, -44]) (count1509 q) 2 1 (meaning1506 q) (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1507 = false ∨ valuation q 1511 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1509 q = (countLit q [-38, -39]) + (countLit q [-42, -44]) := List.countP_append (p := literal q) (l₁ := [-38, -39]) (l₂ := [-42, -44])
  have hm := merge_two (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-38, -39]) (countLit q [-42, -44]) (count1509 q) 2 2 (meaning1506 q) (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = false ∨ valuation q 1512 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 1 (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1513 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 2 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 3 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1516 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1516)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 4 (meaning1512 q) (meaning1516 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1516 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1513 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1513)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 1 (meaning1502 q) (meaning1513 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1513 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 1 1 (meaning1502 q) (meaning1509 q) (meaning1514 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1509 = false ∨ valuation q 1514 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1515)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 1 2 (meaning1502 q) (meaning1510 q) (meaning1515 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1510 = false ∨ valuation q 1515 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1516)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 1 3 (meaning1502 q) (meaning1511 q) (meaning1516 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1511 = false ∨ valuation q 1516 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1517)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 1 4 (meaning1502 q) (meaning1512 q) (meaning1517 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1512 = false ∨ valuation q 1517 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1514 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1514)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 2 (meaning1503 q) (meaning1514 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1514 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 2 1 (meaning1503 q) (meaning1509 q) (meaning1515 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1509 = false ∨ valuation q 1515 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1516)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 2 2 (meaning1503 q) (meaning1510 q) (meaning1516 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1510 = false ∨ valuation q 1516 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1517)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 2 3 (meaning1503 q) (meaning1511 q) (meaning1517 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1511 = false ∨ valuation q 1517 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true := by
  have hs : count1513 q = (countLit q [-32, -34, -37]) + (countLit q [-38, -39, -42, -44]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -37]) (l₂ := [-38, -39, -42, -44])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1518)) (countLit q [-32, -34, -37]) (countLit q [-38, -39, -42, -44]) (count1513 q) 2 4 (meaning1503 q) (meaning1512 q) (meaning1518 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1518 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1512 = false ∨ valuation q 1518 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E040.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112040
