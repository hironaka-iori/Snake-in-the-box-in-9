import E112047Semantics
import B112E047Inputs
namespace Snake9.Regrowth.E112047
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1559 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1539)) (literal (valuationOf q) (1559)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 6 1 (meaning1490 q) (meaning1539 q) (meaning1559 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1539 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1539 = false ∨ valuation q 1559 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1560 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1560)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 6 2 (meaning1490 q) (meaning1540 q) (meaning1560 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1540 = false ∨ valuation q 1560 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 6 3 (meaning1490 q) (meaning1541 q) (meaning1561 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1541 = false ∨ valuation q 1561 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1562 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1562)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 6 4 (meaning1490 q) (meaning1542 q) (meaning1562 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1542 = false ∨ valuation q 1562 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1490 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1563 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1490)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1563)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 6 5 (meaning1490 q) (meaning1543 q) (meaning1563 q) hs
  change valuationOf q 1490 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1490 = false ∨ valuation q 1543 = false ∨ valuation q 1563 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1561 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1540)) (literal (valuationOf q) (1561)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 7 2 (meaning1491 q) (meaning1540 q) (meaning1561 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1540 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1540 = false ∨ valuation q 1561 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1562 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1562)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 7 3 (meaning1491 q) (meaning1541 q) (meaning1562 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1541 = false ∨ valuation q 1562 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1563 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1563)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 7 4 (meaning1491 q) (meaning1542 q) (meaning1563 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1542 = false ∨ valuation q 1563 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1491 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1564 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1491)) (literal (valuationOf q) (1543)) (literal (valuationOf q) (1564)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 7 5 (meaning1491 q) (meaning1543 q) (meaning1564 q) hs
  change valuationOf q 1491 = false ∨ valuationOf q 1543 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1491 = false ∨ valuation q 1543 = false ∨ valuation q 1564 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1563 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1541)) (literal (valuationOf q) (1563)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 8 3 (meaning1492 q) (meaning1541 q) (meaning1563 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1541 = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1541 = false ∨ valuation q 1563 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1492 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1564 = true := by
  have hs : count1553 q = (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) + (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (l₂ := [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1492)) (literal (valuationOf q) (1542)) (literal (valuationOf q) (1564)) (countLit q [-3, -5, -7, -11, -12, -14, -17, -20, -21, -23, -25, -26, -28, -31]) (countLit q [-34, -36, -37, -40, -42, -43, -46, -47, -51, -52, -54, -56, -58, -60]) (count1553 q) 8 4 (meaning1492 q) (meaning1542 q) (meaning1564 q) hs
  change valuationOf q 1492 = false ∨ valuationOf q 1542 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1492 = false ∨ valuation q 1542 = false ∨ valuation q 1564 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1569)) (countLit q [-64]) (countLit q [-66]) (count1569 q) 1 (meaningNeg66 q) (meaning1569 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1569 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 1569 = true := by
  have hs : count1569 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (1569)) (countLit q [-64]) (countLit q [-66]) (count1569 q) 1 (meaningNeg64 q) (meaning1569 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 1569 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1570 = true := by
  have hs : count1569 q = (countLit q [-64]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1570)) (countLit q [-64]) (countLit q [-66]) (count1569 q) 1 1 (meaningNeg64 q) (meaningNeg66 q) (meaning1570 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 66 = true ∨ valuation q 1570 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1569 = false ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1569)) (literal (valuationOf q) (1571)) (countLit q [-63]) (countLit q [-64, -66]) (count1571 q) 1 (meaning1569 q) (meaning1571 q) hs
  change valuationOf q 1569 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1569 = false ∨ valuation q 1571 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 1570 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_right (literal (valuationOf q) (1570)) (literal (valuationOf q) (1572)) (countLit q [-63]) (countLit q [-64, -66]) (count1571 q) 2 (meaning1570 q) (meaning1572 q) hs
  change valuationOf q 1570 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 1570 = false ∨ valuation q 1572 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1571 = true := by
  have hs : count1571 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1571)) (countLit q [-63]) (countLit q [-64, -66]) (count1571 q) 1 (meaningNeg63 q) (meaning1571 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1571 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1569 = false ∨ valuationOf q 1572 = true := by
  have hs : count1571 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1569)) (literal (valuationOf q) (1572)) (countLit q [-63]) (countLit q [-64, -66]) (count1571 q) 1 1 (meaningNeg63 q) (meaning1569 q) (meaning1572 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1569 = false ∨ valuationOf q 1572 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1569 = false ∨ valuation q 1572 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1570 = false ∨ valuationOf q 1573 = true := by
  have hs : count1571 q = (countLit q [-63]) + (countLit q [-64, -66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-64, -66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (1570)) (literal (valuationOf q) (1573)) (countLit q [-63]) (countLit q [-64, -66]) (count1571 q) 1 2 (meaningNeg63 q) (meaning1570 q) (meaning1573 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1570 = false ∨ valuationOf q 1573 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1570 = false ∨ valuation q 1573 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-67]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-71])
  have hm := merge_right (literal (valuationOf q) (-71)) (literal (valuationOf q) (1574)) (countLit q [-67]) (countLit q [-71]) (count1574 q) 1 (meaningNeg71 q) (meaning1574 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1574 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1574 = true := by
  have hs : count1574 q = (countLit q [-67]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-71])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1574)) (countLit q [-67]) (countLit q [-71]) (count1574 q) 1 (meaningNeg67 q) (meaning1574 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1574 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1574 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 71 = true ∨ valuationOf q 1575 = true := by
  have hs : count1574 q = (countLit q [-67]) + (countLit q [-71]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-71])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-71)) (literal (valuationOf q) (1575)) (countLit q [-67]) (countLit q [-71]) (count1574 q) 1 1 (meaningNeg67 q) (meaningNeg71 q) (meaning1575 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 71)) = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 71 = true ∨ valuation q 1575 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_right (literal (valuationOf q) (-75)) (literal (valuationOf q) (1576)) (countLit q [-73]) (countLit q [-75]) (count1576 q) 1 (meaningNeg75 q) (meaning1576 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1576 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1576 = true := by
  have hs : count1576 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (1576)) (countLit q [-73]) (countLit q [-75]) (count1576 q) 1 (meaningNeg73 q) (meaning1576 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1576 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1576 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 75 = true ∨ valuationOf q 1577 = true := by
  have hs : count1576 q = (countLit q [-73]) + (countLit q [-75]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-75])
  have hm := merge_two (literal (valuationOf q) (-73)) (literal (valuationOf q) (-75)) (literal (valuationOf q) (1577)) (countLit q [-73]) (countLit q [-75]) (count1576 q) 1 1 (meaningNeg73 q) (meaningNeg75 q) (meaning1577 q) hs
  change (! (valuationOf q 73)) = false ∨ (! (valuationOf q 75)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 75 = true ∨ valuation q 1577 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1576 = false ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-67, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-67, -71]) (l₂ := [-73, -75])
  have hm := merge_right (literal (valuationOf q) (1576)) (literal (valuationOf q) (1578)) (countLit q [-67, -71]) (countLit q [-73, -75]) (count1578 q) 1 (meaning1576 q) (meaning1578 q) hs
  change valuationOf q 1576 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1576 = false ∨ valuation q 1578 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-67, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-67, -71]) (l₂ := [-73, -75])
  have hm := merge_right (literal (valuationOf q) (1577)) (literal (valuationOf q) (1579)) (countLit q [-67, -71]) (countLit q [-73, -75]) (count1578 q) 2 (meaning1577 q) (meaning1579 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1579 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1578 = true := by
  have hs : count1578 q = (countLit q [-67, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-67, -71]) (l₂ := [-73, -75])
  have hm := merge_left (literal (valuationOf q) (1574)) (literal (valuationOf q) (1578)) (countLit q [-67, -71]) (countLit q [-73, -75]) (count1578 q) 1 (meaning1574 q) (meaning1578 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1578 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-67, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-67, -71]) (l₂ := [-73, -75])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1579)) (countLit q [-67, -71]) (countLit q [-73, -75]) (count1578 q) 1 1 (meaning1574 q) (meaning1576 q) (meaning1579 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1576 = false ∨ valuation q 1579 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 1574 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true := by
  have hs : count1578 q = (countLit q [-67, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-67, -71]) (l₂ := [-73, -75])
  have hm := merge_two (literal (valuationOf q) (1574)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1580)) (countLit q [-67, -71]) (countLit q [-73, -75]) (count1578 q) 1 2 (meaning1574 q) (meaning1577 q) (meaning1580 q) hs
  change valuationOf q 1574 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 1574 = false ∨ valuation q 1577 = false ∨ valuation q 1580 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1579 = true := by
  have hs : count1578 q = (countLit q [-67, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-67, -71]) (l₂ := [-73, -75])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1579)) (countLit q [-67, -71]) (countLit q [-73, -75]) (count1578 q) 2 (meaning1575 q) (meaning1579 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1579 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1580 = true := by
  have hs : count1578 q = (countLit q [-67, -71]) + (countLit q [-73, -75]) := List.countP_append (p := literal q) (l₁ := [-67, -71]) (l₂ := [-73, -75])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1576)) (literal (valuationOf q) (1580)) (countLit q [-67, -71]) (countLit q [-73, -75]) (count1578 q) 2 1 (meaning1575 q) (meaning1576 q) (meaning1580 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1576 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1576 = false ∨ valuation q 1580 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E047.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112047
