import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec36 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1153 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1534 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1534)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 1 2 (meaning1521 q) (meaning1529 q) (meaning1534 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1153 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1529 = false ∨ valuation q 1534 = true := counterClause1153 (baseVal q)

theorem counterClause1154 (q : Nat → Bool) : valuationOf q 1521 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1535 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1521)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1535)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 1 3 (meaning1521 q) (meaning1530 q) (meaning1535 q) hs
  change valuationOf q 1521 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1154 (q : Snake 81) (h : Conditions q) : valuation q 1521 = false ∨ valuation q 1530 = false ∨ valuation q 1535 = true := counterClause1154 (baseVal q)

theorem counterClause1155 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1533 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_left (literal (valuationOf q) (1522)) (literal (valuationOf q) (1533)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 2 (meaning1522 q) (meaning1533 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1155 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1533 = true := counterClause1155 (baseVal q)

theorem counterClause1156 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1534 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1534)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 2 1 (meaning1522 q) (meaning1528 q) (meaning1534 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1534 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1156 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1528 = false ∨ valuation q 1534 = true := counterClause1156 (baseVal q)

theorem counterClause1157 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1535 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1535)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 2 2 (meaning1522 q) (meaning1529 q) (meaning1535 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1157 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1529 = false ∨ valuation q 1535 = true := counterClause1157 (baseVal q)

theorem counterClause1158 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1536 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1536)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 2 3 (meaning1522 q) (meaning1530 q) (meaning1536 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1158 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1530 = false ∨ valuation q 1536 = true := counterClause1158 (baseVal q)

theorem counterClause1159 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1535 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1528)) (literal (valuationOf q) (1535)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 3 1 (meaning1523 q) (meaning1528 q) (meaning1535 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1528 = false ∨ valuationOf q 1535 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1159 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1528 = false ∨ valuation q 1535 = true := counterClause1159 (baseVal q)

theorem counterClause1160 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1536 = true := by
  have hs : count1532 q = (countLit q [-47, -51, -52]) + (countLit q [-54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-47, -51, -52]) (l₂ := [-54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1523)) (literal (valuationOf q) (1529)) (literal (valuationOf q) (1536)) (countLit q [-47, -51, -52]) (countLit q [-54, -56, -58, -60]) (count1532 q) 3 2 (meaning1523 q) (meaning1529 q) (meaning1536 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1529 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1160 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1529 = false ∨ valuation q 1536 = true := counterClause1160 (baseVal q)

theorem counterClause1161 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1532)) (literal (valuationOf q) (1539)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 1 (meaning1532 q) (meaning1539 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1161 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1539 = true := counterClause1161 (baseVal q)

theorem counterClause1162 (q : Nat → Bool) : valuationOf q 1534 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1534)) (literal (valuationOf q) (1541)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 3 (meaning1534 q) (meaning1541 q) hs
  change valuationOf q 1534 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1162 (q : Snake 81) (h : Conditions q) : valuation q 1534 = false ∨ valuation q 1541 = true := counterClause1162 (baseVal q)

theorem counterClause1163 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1540)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 1 1 (meaning1512 q) (meaning1532 q) (meaning1540 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1163 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1532 = false ∨ valuation q 1540 = true := counterClause1163 (baseVal q)

theorem counterClause1164 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1541)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 1 2 (meaning1512 q) (meaning1533 q) (meaning1541 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1164 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1533 = false ∨ valuation q 1541 = true := counterClause1164 (baseVal q)

theorem counterClause1165 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1542)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 1 3 (meaning1512 q) (meaning1534 q) (meaning1542 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1165 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1534 = false ∨ valuation q 1542 = true := counterClause1165 (baseVal q)

theorem counterClause1166 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1543)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 1 4 (meaning1512 q) (meaning1535 q) (meaning1543 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1166 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1535 = false ∨ valuation q 1543 = true := counterClause1166 (baseVal q)

theorem counterClause1167 (q : Nat → Bool) : valuationOf q 1512 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1512)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1544)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 1 5 (meaning1512 q) (meaning1536 q) (meaning1544 q) hs
  change valuationOf q 1512 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1167 (q : Snake 81) (h : Conditions q) : valuation q 1512 = false ∨ valuation q 1536 = false ∨ valuation q 1544 = true := counterClause1167 (baseVal q)

theorem counterClause1168 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1541)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 2 1 (meaning1513 q) (meaning1532 q) (meaning1541 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1168 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1532 = false ∨ valuation q 1541 = true := counterClause1168 (baseVal q)

theorem counterClause1169 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1542)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 2 2 (meaning1513 q) (meaning1533 q) (meaning1542 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1169 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1533 = false ∨ valuation q 1542 = true := counterClause1169 (baseVal q)

theorem counterClause1170 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1543)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 2 3 (meaning1513 q) (meaning1534 q) (meaning1543 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1170 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1534 = false ∨ valuation q 1543 = true := counterClause1170 (baseVal q)

theorem counterClause1171 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1544)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 2 4 (meaning1513 q) (meaning1535 q) (meaning1544 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1171 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1535 = false ∨ valuation q 1544 = true := counterClause1171 (baseVal q)

theorem counterClause1172 (q : Nat → Bool) : valuationOf q 1513 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1545 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1513)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1545)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 2 5 (meaning1513 q) (meaning1536 q) (meaning1545 q) hs
  change valuationOf q 1513 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1172 (q : Snake 81) (h : Conditions q) : valuation q 1513 = false ∨ valuation q 1536 = false ∨ valuation q 1545 = true := counterClause1172 (baseVal q)

theorem counterClause1173 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_left (literal (valuationOf q) (1514)) (literal (valuationOf q) (1541)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 3 (meaning1514 q) (meaning1541 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1173 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1541 = true := counterClause1173 (baseVal q)

theorem counterClause1174 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1542)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 3 1 (meaning1514 q) (meaning1532 q) (meaning1542 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1174 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1532 = false ∨ valuation q 1542 = true := counterClause1174 (baseVal q)

theorem counterClause1175 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1543)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 3 2 (meaning1514 q) (meaning1533 q) (meaning1543 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1175 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1533 = false ∨ valuation q 1543 = true := counterClause1175 (baseVal q)

theorem counterClause1176 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1544)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 3 3 (meaning1514 q) (meaning1534 q) (meaning1544 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1176 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1534 = false ∨ valuation q 1544 = true := counterClause1176 (baseVal q)

theorem counterClause1177 (q : Nat → Bool) : valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1514)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1545)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 3 4 (meaning1514 q) (meaning1535 q) (meaning1545 q) hs
  change valuationOf q 1514 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1177 (q : Snake 81) (h : Conditions q) : valuation q 1514 = false ∨ valuation q 1535 = false ∨ valuation q 1545 = true := counterClause1177 (baseVal q)

theorem counterClause1178 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_left (literal (valuationOf q) (1515)) (literal (valuationOf q) (1542)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 4 (meaning1515 q) (meaning1542 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1178 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1542 = true := counterClause1178 (baseVal q)

theorem counterClause1179 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1543 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1543)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 4 1 (meaning1515 q) (meaning1532 q) (meaning1543 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1543 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1179 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1532 = false ∨ valuation q 1543 = true := counterClause1179 (baseVal q)

theorem counterClause1180 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1544 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1544)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 4 2 (meaning1515 q) (meaning1533 q) (meaning1544 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1544 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1180 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1533 = false ∨ valuation q 1544 = true := counterClause1180 (baseVal q)

theorem counterClause1181 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1545 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1534)) (literal (valuationOf q) (1545)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 4 3 (meaning1515 q) (meaning1534 q) (meaning1545 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1534 = false ∨ valuationOf q 1545 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1181 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1534 = false ∨ valuation q 1545 = true := counterClause1181 (baseVal q)

theorem counterClause1182 (q : Nat → Bool) : valuationOf q 1515 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1546 = true := by
  have hs : count1539 q = (countLit q [-34, -36, -37, -40, -42, -43, -46]) + (countLit q [-47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-34, -36, -37, -40, -42, -43, -46]) (l₂ := [-47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1515)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1546)) (countLit q [-34, -36, -37, -40, -42, -43, -46]) (countLit q [-47, -51, -52, -54, -56, -58, -60]) (count1539 q) 4 4 (meaning1515 q) (meaning1535 q) (meaning1546 q) hs
  change valuationOf q 1515 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1182 (q : Snake 81) (h : Conditions q) : valuation q 1515 = false ∨ valuation q 1535 = false ∨ valuation q 1546 = true := counterClause1182 (baseVal q)

theorem counterClause1183 (q : Nat → Bool) : valuationOf q 1545 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1545)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 7 (meaning1545 q) (meaning1559 q) hs
  change valuationOf q 1545 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1183 (q : Snake 81) (h : Conditions q) : valuation q 1545 = false ∨ valuation q 1559 = true := counterClause1183 (baseVal q)

theorem counterClause1184 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1555 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1555)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 1 2 (meaning1485 q) (meaning1540 q) (meaning1555 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1184 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1540 = false ∨ valuation q 1555 = true := counterClause1184 (baseVal q)

theorem block36 (q : Snake 81) (h : Conditions q) : B112E047.Block36 (valuation q) :=
  ⟨clause1153 q h, clause1154 q h, clause1155 q h, clause1156 q h, clause1157 q h, clause1158 q h, clause1159 q h, clause1160 q h, clause1161 q h, clause1162 q h, clause1163 q h, clause1164 q h, clause1165 q h, clause1166 q h, clause1167 q h, clause1168 q h, clause1169 q h, clause1170 q h, clause1171 q h, clause1172 q h, clause1173 q h, clause1174 q h, clause1175 q h, clause1176 q h, clause1177 q h, clause1178 q h, clause1179 q h, clause1180 q h, clause1181 q h, clause1182 q h, clause1183 q h, clause1184 q h⟩

end
end Snake9.Regrowth.E112047
