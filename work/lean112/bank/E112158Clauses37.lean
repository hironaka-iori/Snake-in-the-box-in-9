import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1501 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1501)) (literal (valuationOf q) (1510)) (literal (valuationOf q) (1517)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 3 4 (meaning1501 q) (meaning1510 q) (meaning1517 q) hs
  change valuationOf q 1501 = false ∨ valuationOf q 1510 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1501 = false ∨ valuation q 1510 = false ∨ valuation q 1517 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1514 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_left (literal (valuationOf q) (1502)) (literal (valuationOf q) (1514)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 4 (meaning1502 q) (meaning1514 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1514 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1514 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1515 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1507)) (literal (valuationOf q) (1515)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 4 1 (meaning1502 q) (meaning1507 q) (meaning1515 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1507 = false ∨ valuationOf q 1515 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1507 = false ∨ valuation q 1515 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1516 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1508)) (literal (valuationOf q) (1516)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 4 2 (meaning1502 q) (meaning1508 q) (meaning1516 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1508 = false ∨ valuationOf q 1516 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1508 = false ∨ valuation q 1516 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1517 = true := by
  have hs : count1511 q = (countLit q [-45, -48, -50, -51]) + (countLit q [-53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-45, -48, -50, -51]) (l₂ := [-53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1502)) (literal (valuationOf q) (1509)) (literal (valuationOf q) (1517)) (countLit q [-45, -48, -50, -51]) (countLit q [-53, -54, -55, -58]) (count1511 q) 4 3 (meaning1502 q) (meaning1509 q) (meaning1517 q) hs
  change valuationOf q 1502 = false ∨ valuationOf q 1509 = false ∨ valuationOf q 1517 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1502 = false ∨ valuation q 1509 = false ∨ valuation q 1517 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1512)) (literal (valuationOf q) (1520)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 2 (meaning1512 q) (meaning1520 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1520 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1521 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1513)) (literal (valuationOf q) (1521)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 3 (meaning1513 q) (meaning1521 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1521 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1522 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1514)) (literal (valuationOf q) (1522)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 4 (meaning1514 q) (meaning1522 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1522 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1523 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1515)) (literal (valuationOf q) (1523)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 5 (meaning1515 q) (meaning1523 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1523 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1516 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1516)) (literal (valuationOf q) (1524)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 6 (meaning1516 q) (meaning1524 q) hs
  change valuationOf q 1516 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1516 = false ∨ valuation q 1524 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_right (literal (valuationOf q) (1517)) (literal (valuationOf q) (1525)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 7 (meaning1517 q) (meaning1525 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1525 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1520)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 1 1 (meaning1488 q) (meaning1511 q) (meaning1520 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1511 = false ∨ valuation q 1520 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1521 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1521)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 1 2 (meaning1488 q) (meaning1512 q) (meaning1521 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1512 = false ∨ valuation q 1521 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1522 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1522)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 1 3 (meaning1488 q) (meaning1513 q) (meaning1522 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1513 = false ∨ valuation q 1522 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1523 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1523)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 1 4 (meaning1488 q) (meaning1514 q) (meaning1523 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1514 = false ∨ valuation q 1523 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1524)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 1 5 (meaning1488 q) (meaning1515 q) (meaning1524 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1515 = false ∨ valuation q 1524 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1525)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 1 6 (meaning1488 q) (meaning1516 q) (meaning1525 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1516 = false ∨ valuation q 1525 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1526 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1526)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 1 7 (meaning1488 q) (meaning1517 q) (meaning1526 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1517 = false ∨ valuation q 1526 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1521 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1521)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 2 1 (meaning1489 q) (meaning1511 q) (meaning1521 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1521 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1511 = false ∨ valuation q 1521 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1522 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1522)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 2 2 (meaning1489 q) (meaning1512 q) (meaning1522 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1512 = false ∨ valuation q 1522 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1523 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1523)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 2 3 (meaning1489 q) (meaning1513 q) (meaning1523 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1513 = false ∨ valuation q 1523 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1524)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 2 4 (meaning1489 q) (meaning1514 q) (meaning1524 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1514 = false ∨ valuation q 1524 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1525)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 2 5 (meaning1489 q) (meaning1515 q) (meaning1525 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1515 = false ∨ valuation q 1525 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1526 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1526)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 2 6 (meaning1489 q) (meaning1516 q) (meaning1526 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1516 = false ∨ valuation q 1526 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1527 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1517)) (literal (valuationOf q) (1527)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 2 7 (meaning1489 q) (meaning1517 q) (meaning1527 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1517 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1517 = false ∨ valuation q 1527 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1522 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1522)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 3 1 (meaning1490 q) (meaning1511 q) (meaning1522 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1511 = false ∨ valuation q 1522 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1523 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1512)) (literal (valuationOf q) (1523)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 3 2 (meaning1490 q) (meaning1512 q) (meaning1523 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1512 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1512 = false ∨ valuation q 1523 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1524 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1513)) (literal (valuationOf q) (1524)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 3 3 (meaning1490 q) (meaning1513 q) (meaning1524 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1513 = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1513 = false ∨ valuation q 1524 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1525 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1514)) (literal (valuationOf q) (1525)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 3 4 (meaning1490 q) (meaning1514 q) (meaning1525 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1514 = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1514 = false ∨ valuation q 1525 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1526 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1515)) (literal (valuationOf q) (1526)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 3 5 (meaning1490 q) (meaning1515 q) (meaning1526 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1515 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1515 = false ∨ valuation q 1526 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1527 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1516)) (literal (valuationOf q) (1527)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 3 6 (meaning1490 q) (meaning1516 q) (meaning1527 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1516 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1516 = false ∨ valuation q 1527 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1523 = true := by
  have hs : count1519 q = (countLit q [-32, -34, -35, -39, -41, -42, -44]) + (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -39, -41, -42, -44]) (l₂ := [-45, -48, -50, -51, -53, -54, -55, -58])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1511)) (literal (valuationOf q) (1523)) (countLit q [-32, -34, -35, -39, -41, -42, -44]) (countLit q [-45, -48, -50, -51, -53, -54, -55, -58]) (count1519 q) 4 1 (meaning1491 q) (meaning1511 q) (meaning1523 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1511 = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1511 = false ∨ valuation q 1523 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E158.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112158
