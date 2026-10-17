import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec37 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1185 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1556 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 1 3 (meaning1485 q) (meaning1541 q) (meaning1556 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1185 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1541 = false ∨ valuation q 1556 = true := counterClause1185 (baseVal q)

theorem counterClause1186 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 1 4 (meaning1485 q) (meaning1542 q) (meaning1557 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1186 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1542 = false ∨ valuation q 1557 = true := counterClause1186 (baseVal q)

theorem counterClause1187 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 1 5 (meaning1485 q) (meaning1543 q) (meaning1558 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1187 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1543 = false ∨ valuation q 1558 = true := counterClause1187 (baseVal q)

theorem counterClause1188 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 1 6 (meaning1485 q) (meaning1544 q) (meaning1559 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1188 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1544 = false ∨ valuation q 1559 = true := counterClause1188 (baseVal q)

theorem counterClause1189 (q : Nat → Bool) : valuationOf q 1485 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1485)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 1 7 (meaning1485 q) (meaning1545 q) (meaning1560 q) hs
  change valuationOf q 1485 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1189 (q : Snake 81) (h : Conditions q) : valuation q 1485 = false ∨ valuation q 1545 = false ∨ valuation q 1560 = true := counterClause1189 (baseVal q)

theorem counterClause1190 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1556 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 2 2 (meaning1486 q) (meaning1540 q) (meaning1556 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1190 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1540 = false ∨ valuation q 1556 = true := counterClause1190 (baseVal q)

theorem counterClause1191 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 2 3 (meaning1486 q) (meaning1541 q) (meaning1557 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1191 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1541 = false ∨ valuation q 1557 = true := counterClause1191 (baseVal q)

theorem counterClause1192 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 2 4 (meaning1486 q) (meaning1542 q) (meaning1558 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1192 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1542 = false ∨ valuation q 1558 = true := counterClause1192 (baseVal q)

theorem counterClause1193 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 2 5 (meaning1486 q) (meaning1543 q) (meaning1559 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1193 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1543 = false ∨ valuation q 1559 = true := counterClause1193 (baseVal q)

theorem counterClause1194 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 2 6 (meaning1486 q) (meaning1544 q) (meaning1560 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1194 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1544 = false ∨ valuation q 1560 = true := counterClause1194 (baseVal q)

theorem counterClause1195 (q : Nat → Bool) : valuationOf q 1486 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1486)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 2 7 (meaning1486 q) (meaning1545 q) (meaning1561 q) hs
  change valuationOf q 1486 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1195 (q : Snake 81) (h : Conditions q) : valuation q 1486 = false ∨ valuation q 1545 = false ∨ valuation q 1561 = true := counterClause1195 (baseVal q)

theorem counterClause1196 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1556 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1556)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 3 1 (meaning1487 q) (meaning1539 q) (meaning1556 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1196 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1539 = false ∨ valuation q 1556 = true := counterClause1196 (baseVal q)

theorem counterClause1197 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 3 2 (meaning1487 q) (meaning1540 q) (meaning1557 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1197 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1540 = false ∨ valuation q 1557 = true := counterClause1197 (baseVal q)

theorem counterClause1198 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 3 3 (meaning1487 q) (meaning1541 q) (meaning1558 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1198 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1541 = false ∨ valuation q 1558 = true := counterClause1198 (baseVal q)

theorem counterClause1199 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 3 4 (meaning1487 q) (meaning1542 q) (meaning1559 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1199 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1542 = false ∨ valuation q 1559 = true := counterClause1199 (baseVal q)

theorem counterClause1200 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 3 5 (meaning1487 q) (meaning1543 q) (meaning1560 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1200 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1543 = false ∨ valuation q 1560 = true := counterClause1200 (baseVal q)

theorem counterClause1201 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 3 6 (meaning1487 q) (meaning1544 q) (meaning1561 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1201 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1544 = false ∨ valuation q 1561 = true := counterClause1201 (baseVal q)

theorem counterClause1202 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1562 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1562)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 3 7 (meaning1487 q) (meaning1545 q) (meaning1562 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1202 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1545 = false ∨ valuation q 1562 = true := counterClause1202 (baseVal q)

theorem counterClause1203 (q : Nat → Bool) : valuationOf q 1487 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1563 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1487)) (literal (valuationOf q) (1546)) (literal (valuationOf q) (1563)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 3 8 (meaning1487 q) (meaning1546 q) (meaning1563 q) hs
  change valuationOf q 1487 = false ∨ valuationOf q 1546 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1203 (q : Snake 81) (h : Conditions q) : valuation q 1487 = false ∨ valuation q 1546 = false ∨ valuation q 1563 = true := counterClause1203 (baseVal q)

theorem counterClause1204 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1557 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1557)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 4 1 (meaning1488 q) (meaning1539 q) (meaning1557 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1204 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1539 = false ∨ valuation q 1557 = true := counterClause1204 (baseVal q)

theorem counterClause1205 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 4 2 (meaning1488 q) (meaning1540 q) (meaning1558 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1205 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1540 = false ∨ valuation q 1558 = true := counterClause1205 (baseVal q)

theorem counterClause1206 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 4 3 (meaning1488 q) (meaning1541 q) (meaning1559 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1206 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1541 = false ∨ valuation q 1559 = true := counterClause1206 (baseVal q)

theorem counterClause1207 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 4 4 (meaning1488 q) (meaning1542 q) (meaning1560 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1207 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1542 = false ∨ valuation q 1560 = true := counterClause1207 (baseVal q)

theorem counterClause1208 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 4 5 (meaning1488 q) (meaning1543 q) (meaning1561 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1208 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1543 = false ∨ valuation q 1561 = true := counterClause1208 (baseVal q)

theorem counterClause1209 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1562 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1562)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 4 6 (meaning1488 q) (meaning1544 q) (meaning1562 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1209 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1544 = false ∨ valuation q 1562 = true := counterClause1209 (baseVal q)

theorem counterClause1210 (q : Nat → Bool) : valuationOf q 1488 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1563 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1488)) (literal (valuationOf q) (1545)) (literal (valuationOf q) (1563)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 4 7 (meaning1488 q) (meaning1545 q) (meaning1563 q) hs
  change valuationOf q 1488 = false ∨ valuationOf q 1545 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1210 (q : Snake 81) (h : Conditions q) : valuation q 1488 = false ∨ valuation q 1545 = false ∨ valuation q 1563 = true := counterClause1210 (baseVal q)

theorem counterClause1211 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1558 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1558)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 5 1 (meaning1489 q) (meaning1539 q) (meaning1558 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1211 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1539 = false ∨ valuation q 1558 = true := counterClause1211 (baseVal q)

theorem counterClause1212 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 5 2 (meaning1489 q) (meaning1540 q) (meaning1559 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1212 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1540 = false ∨ valuation q 1559 = true := counterClause1212 (baseVal q)

theorem counterClause1213 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 5 3 (meaning1489 q) (meaning1541 q) (meaning1560 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1213 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1541 = false ∨ valuation q 1560 = true := counterClause1213 (baseVal q)

theorem counterClause1214 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 5 4 (meaning1489 q) (meaning1542 q) (meaning1561 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1214 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1542 = false ∨ valuation q 1561 = true := counterClause1214 (baseVal q)

theorem counterClause1215 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1562 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1562)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 5 5 (meaning1489 q) (meaning1543 q) (meaning1562 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1215 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1543 = false ∨ valuation q 1562 = true := counterClause1215 (baseVal q)

theorem counterClause1216 (q : Nat → Bool) : valuationOf q 1489 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1563 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1489)) (literal (valuationOf q) (1544)) (literal (valuationOf q) (1563)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 5 6 (meaning1489 q) (meaning1544 q) (meaning1563 q) hs
  change valuationOf q 1489 = false ∨ valuationOf q 1544 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1216 (q : Snake 81) (h : Conditions q) : valuation q 1489 = false ∨ valuation q 1544 = false ∨ valuation q 1563 = true := counterClause1216 (baseVal q)

theorem block37 (q : Snake 81) (h : Conditions q) : B112E047.Block37 (valuation q) :=
  ⟨clause1185 q h, clause1186 q h, clause1187 q h, clause1188 q h, clause1189 q h, clause1190 q h, clause1191 q h, clause1192 q h, clause1193 q h, clause1194 q h, clause1195 q h, clause1196 q h, clause1197 q h, clause1198 q h, clause1199 q h, clause1200 q h, clause1201 q h, clause1202 q h, clause1203 q h, clause1204 q h, clause1205 q h, clause1206 q h, clause1207 q h, clause1208 q h, clause1209 q h, clause1210 q h, clause1211 q h, clause1212 q h, clause1213 q h, clause1214 q h, clause1215 q h, clause1216 q h⟩

end
end Snake9.Regrowth.E112047
