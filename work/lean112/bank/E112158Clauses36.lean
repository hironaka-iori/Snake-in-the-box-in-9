import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1503)) (countLit q [-53]) (countLit q [-54]) (count1503 q) 1 (meaningNeg54 q) (meaning1503 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1503 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1503 = true := by
  have hs : count1503 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1503)) (countLit q [-53]) (countLit q [-54]) (count1503 q) 1 (meaningNeg53 q) (meaning1503 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1503 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1503 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1504 = true := by
  have hs : count1503 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1504)) (countLit q [-53]) (countLit q [-54]) (count1503 q) 1 1 (meaningNeg53 q) (meaningNeg54 q) (meaning1504 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1504 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 54 = true ∨ valuation q 1504 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1505)) (countLit q [-55]) (countLit q [-58]) (count1505 q) 1 (meaningNeg58 q) (meaning1505 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1505 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1505 = true := by
  have hs : count1505 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1505)) (countLit q [-55]) (countLit q [-58]) (count1505 q) 1 (meaningNeg55 q) (meaning1505 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1505 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1505 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 58 = true ∨ valuationOf q 1506 = true := by
  have hs : count1505 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (1506)) (countLit q [-55]) (countLit q [-58]) (count1505 q) 1 1 (meaningNeg55 q) (meaningNeg58 q) (meaning1506 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 1506 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 58 = true ∨ valuation q 1506 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1505 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-53, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -58])
  have hm := merge_right (literal (valuationOf q) (1505)) (literal (valuationOf q) (1507)) (countLit q [-53, -54]) (countLit q [-55, -58]) (count1507 q) 1 (meaning1505 q) (meaning1507 q) hs
  change valuationOf q 1505 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1505 = false ∨ valuation q 1507 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1506 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-53, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -58])
  have hm := merge_right (literal (valuationOf q) (1506)) (literal (valuationOf q) (1508)) (countLit q [-53, -54]) (countLit q [-55, -58]) (count1507 q) 2 (meaning1506 q) (meaning1508 q) hs
  change valuationOf q 1506 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1506 = false ∨ valuation q 1508 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1507 = true := by
  have hs : count1507 q = (countLit q [-53, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -58])
  have hm := merge_left (literal (valuationOf q) (1503)) (literal (valuationOf q) (1507)) (countLit q [-53, -54]) (countLit q [-55, -58]) (count1507 q) 1 (meaning1503 q) (meaning1507 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1507 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1507 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-53, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -58])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1508)) (countLit q [-53, -54]) (countLit q [-55, -58]) (count1507 q) 1 1 (meaning1503 q) (meaning1505 q) (meaning1508 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1505 = false ∨ valuation q 1508 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1503 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-53, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -58])
  have hm := merge_two (literal (valuationOf q) (1503)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1509)) (countLit q [-53, -54]) (countLit q [-55, -58]) (count1507 q) 1 2 (meaning1503 q) (meaning1506 q) (meaning1509 q) hs
  change valuationOf q 1503 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1503 = false ∨ valuation q 1506 = false ∨ valuation q 1509 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1508 = true := by
  have hs : count1507 q = (countLit q [-53, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -58])
  have hm := merge_left (literal (valuationOf q) (1504)) (literal (valuationOf q) (1508)) (countLit q [-53, -54]) (countLit q [-55, -58]) (count1507 q) 2 (meaning1504 q) (meaning1508 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1508 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1508 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1509 = true := by
  have hs : count1507 q = (countLit q [-53, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -58])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1505)) (literal (valuationOf q) (1509)) (countLit q [-53, -54]) (countLit q [-55, -58]) (count1507 q) 2 1 (meaning1504 q) (meaning1505 q) (meaning1509 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1505 = false ∨ valuationOf q 1509 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1505 = false ∨ valuation q 1509 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1504 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1510 = true := by
  have hs : count1507 q = (countLit q [-53, -54]) + (countLit q [-55, -58]) := List.countP_append (p := literal q) (l₁ := [-53, -54]) (l₂ := [-55, -58])
  have hm := merge_two (literal (valuationOf q) (1504)) (literal (valuationOf q) (1506)) (literal (valuationOf q) (1510)) (countLit q [-53, -54]) (countLit q [-55, -58]) (count1507 q) 2 2 (meaning1504 q) (meaning1506 q) (meaning1510 q) hs
  change valuationOf q 1504 = false ∨ valuationOf q 1506 = false ∨ valuationOf q 1510 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1504 = false ∨ valuation q 1506 = false ∨ valuation q 1510 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1507 = false ∨ valuationOf q 1511 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1507)) (literal (valuationOf q) (1511)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 1 (meaning1507 q) (meaning1511 q) hs
  change valuationOf q 1507 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1507 = false ∨ valuation q 1511 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1508 = false ∨ valuationOf q 1512 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1508)) (literal (valuationOf q) (1512)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 2 (meaning1508 q) (meaning1512 q) hs
  change valuationOf q 1508 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1508 = false ∨ valuation q 1512 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1509 = false ∨ valuationOf q 1513 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1509)) (literal (valuationOf q) (1513)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 3 (meaning1509 q) (meaning1513 q) hs
  change valuationOf q 1509 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1509 = false ∨ valuation q 1513 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1514 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1510)) (literal (valuationOf q) (1514)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 4 (meaning1510 q) (meaning1514 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1514 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1511 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1499)) (literal (valuationOf q) (1511)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 1 (meaning1499 q) (meaning1511 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1511 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1511 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1512)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 1 1 (meaning1499 q) (meaning1507 q) (meaning1512 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1507 = false ∨ valuation q 1512 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1513)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 1 2 (meaning1499 q) (meaning1508 q) (meaning1513 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1508 = false ∨ valuation q 1513 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1514)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 1 3 (meaning1499 q) (meaning1509 q) (meaning1514 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1509 = false ∨ valuation q 1514 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1499 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1499)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1515)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 1 4 (meaning1499 q) (meaning1510 q) (meaning1515 q) hs
  change valuationOf q 1499 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1499 = false ∨ valuation q 1510 = false ∨ valuation q 1515 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1512 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1500)) (literal (valuationOf q) (1512)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 2 (meaning1500 q) (meaning1512 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1512 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1512 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1513)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 2 1 (meaning1500 q) (meaning1507 q) (meaning1513 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1507 = false ∨ valuation q 1513 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1514)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 2 2 (meaning1500 q) (meaning1508 q) (meaning1514 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1508 = false ∨ valuation q 1514 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1515)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 2 3 (meaning1500 q) (meaning1509 q) (meaning1515 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1509 = false ∨ valuation q 1515 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1500 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1500)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1516)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 2 4 (meaning1500 q) (meaning1510 q) (meaning1516 q) hs
  change valuationOf q 1500 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1500 = false ∨ valuation q 1510 = false ∨ valuation q 1516 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1513 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1501)) (literal (valuationOf q) (1513)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 3 (meaning1501 q) (meaning1513 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1513 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1513 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1514 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1514)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 3 1 (meaning1501 q) (meaning1507 q) (meaning1514 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1507 = false ∨ valuation q 1514 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1515 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1515)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 3 2 (meaning1501 q) (meaning1508 q) (meaning1515 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1508 = false ∨ valuation q 1515 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1516 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1516)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 3 3 (meaning1501 q) (meaning1509 q) (meaning1516 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1509 = false ∨ valuation q 1516 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E158.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112158
