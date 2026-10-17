import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1512 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 2 (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1513 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 3 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1515 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_right (literal (valuationOf q) (1511)) (literal (valuationOf q) (1515)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 4 (meaning1511 q) (meaning1515 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1515 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1512 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1512)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 (meaning1501 q) (meaning1512 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1512 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1513)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 1 (meaning1501 q) (meaning1508 q) (meaning1513 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1508 = false ∨ valuation q 1513 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 1 2 (meaning1501 q) (meaning1509 q) (meaning1514 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1509 = false ∨ valuation q 1514 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1513 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1513)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 2 (meaning1502 q) (meaning1513 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1513 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 2 1 (meaning1502 q) (meaning1508 q) (meaning1514 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1508 = false ∨ valuation q 1514 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 2 2 (meaning1502 q) (meaning1509 q) (meaning1515 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1509 = false ∨ valuation q 1515 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1515 = true := by
  have hs : count1512 q = (countLit q [-34, -36, -37]) + (countLit q [-40, -42, -43, -46]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37]) (l₂ := [-40, -42, -43, -46])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (countLit q [-34, -36, -37]) (countLit q [-40, -42, -43, -46]) (count1512 q) 3 1 (meaning1503 q) (meaning1508 q) (meaning1515 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1508 = false ∨ valuation q 1515 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_right (literal (valuationOf q) (-52)) (literal (valuationOf q) (1519)) (countLit q [-51]) (countLit q [-52]) (count1519 q) 1 (meaningNeg52 q) (meaning1519 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1519 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1519)) (countLit q [-51]) (countLit q [-52]) (count1519 q) 1 (meaningNeg51 q) (meaning1519 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1519 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 52 = true ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-51]) + (countLit q [-52]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-52])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-52)) (literal (valuationOf q) (1520)) (countLit q [-51]) (countLit q [-52]) (count1519 q) 1 1 (meaningNeg51 q) (meaningNeg52 q) (meaning1520 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 52)) = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 52 = true ∨ valuation q 1520 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-47]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1519)) (literal (valuationOf q) (1521)) (countLit q [-47]) (countLit q [-51, -52]) (count1521 q) 1 (meaning1519 q) (meaning1521 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1521 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-47]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51, -52])
  have hm := merge_right (literal (valuationOf q) (1520)) (literal (valuationOf q) (1522)) (countLit q [-47]) (countLit q [-51, -52]) (count1521 q) 2 (meaning1520 q) (meaning1522 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1522 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1521 = true := by
  have hs : count1521 q = (countLit q [-47]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51, -52])
  have hm := merge_left (literal (valuationOf q) (-47)) (literal (valuationOf q) (1521)) (countLit q [-47]) (countLit q [-51, -52]) (count1521 q) 1 (meaningNeg47 q) (meaning1521 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1521 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true := by
  have hs : count1521 q = (countLit q [-47]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (1519)) (literal (valuationOf q) (1522)) (countLit q [-47]) (countLit q [-51, -52]) (count1521 q) 1 1 (meaningNeg47 q) (meaning1519 q) (meaning1522 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1519 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1519 = false ∨ valuation q 1522 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 1520 = false ∨ valuationOf q 1523 = true := by
  have hs : count1521 q = (countLit q [-47]) + (countLit q [-51, -52]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-51, -52])
  have hm := merge_two (literal (valuationOf q) (-47)) (literal (valuationOf q) (1520)) (literal (valuationOf q) (1523)) (countLit q [-47]) (countLit q [-51, -52]) (count1521 q) 1 2 (meaningNeg47 q) (meaning1520 q) (meaning1523 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 1520 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 1520 = false ∨ valuation q 1523 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (1524)) (countLit q [-54]) (countLit q [-56]) (count1524 q) 1 (meaningNeg56 q) (meaning1524 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1524 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-54)) (literal (valuationOf q) (1524)) (countLit q [-54]) (countLit q [-56]) (count1524 q) 1 (meaningNeg54 q) (meaning1524 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1524 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1525)) (countLit q [-54]) (countLit q [-56]) (count1524 q) 1 1 (meaningNeg54 q) (meaningNeg56 q) (meaning1525 q) hs
  change (! (valuationOf q 54)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 56 = true ∨ valuation q 1525 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1526)) (countLit q [-58]) (countLit q [-60]) (count1526 q) 1 (meaningNeg58 q) (meaning1526 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1526 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-54, -56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-58, -60])
  have hm := merge_right (literal (valuationOf q) (1526)) (literal (valuationOf q) (1528)) (countLit q [-54, -56]) (countLit q [-58, -60]) (count1528 q) 1 (meaning1526 q) (meaning1528 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1528 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1528 = true := by
  have hs : count1528 q = (countLit q [-54, -56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-58, -60])
  have hm := merge_left (literal (valuationOf q) (1524)) (literal (valuationOf q) (1528)) (countLit q [-54, -56]) (countLit q [-58, -60]) (count1528 q) 1 (meaning1524 q) (meaning1528 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1528 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1528 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-54, -56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-58, -60])
  have hm := merge_two (literal (valuationOf q) (1524)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1529)) (countLit q [-54, -56]) (countLit q [-58, -60]) (count1528 q) 1 1 (meaning1524 q) (meaning1526 q) (meaning1529 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1526 = false ∨ valuation q 1529 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1529 = true := by
  have hs : count1528 q = (countLit q [-54, -56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-58, -60])
  have hm := merge_left (literal (valuationOf q) (1525)) (literal (valuationOf q) (1529)) (countLit q [-54, -56]) (countLit q [-58, -60]) (count1528 q) 2 (meaning1525 q) (meaning1529 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1529 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1529 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1528 q = (countLit q [-54, -56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-54, -56]) (l₂ := [-58, -60])
  have hm := merge_two (literal (valuationOf q) (1525)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-54, -56]) (countLit q [-58, -60]) (count1528 q) 2 1 (meaning1525 q) (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1526 = false ∨ valuation q 1530 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1532 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1528)) (literal (valuationOf q) (1532)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 1 (meaning1528 q) (meaning1532 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1532 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1533 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1529)) (literal (valuationOf q) (1533)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 2 (meaning1529 q) (meaning1533 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1533 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 1530 = false ∨ valuationOf q 1534 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1530)) (literal (valuationOf q) (1534)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 3 (meaning1530 q) (meaning1534 q) hs
  change valuationOf q 1530 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 1530 = false ∨ valuation q 1534 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1533 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1533)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 1 1 (meaning1521 q) (meaning1528 q) (meaning1533 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1528 = false ∨ valuation q 1533 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E047.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112047
