import E112034Semantics
import B112E034Inputs
namespace Snake9.Regrowth.E112034
noncomputable section
local instance blockDec39 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1249 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1633 = true := by
  have hs : count1632 q = (countLit q [-44, -46]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -51])
  have hm := merge_left (literal (valuationOf q) (1629)) (literal (valuationOf q) (1633)) (countLit q [-44, -46]) (countLit q [-48, -51]) (count1632 q) 2 (meaning1629 q) (meaning1633 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1633 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1249 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1633 = true := counterClause1249 (baseVal q)

theorem counterClause1250 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true := by
  have hs : count1632 q = (countLit q [-44, -46]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -51])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1634)) (countLit q [-44, -46]) (countLit q [-48, -51]) (count1632 q) 2 1 (meaning1629 q) (meaning1630 q) (meaning1634 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1250 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1630 = false ∨ valuation q 1634 = true := counterClause1250 (baseVal q)

theorem counterClause1251 (q : Nat → Bool) : valuationOf q 1629 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1635 = true := by
  have hs : count1632 q = (countLit q [-44, -46]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -51])
  have hm := merge_two (literal (valuationOf q) (1629)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1635)) (countLit q [-44, -46]) (countLit q [-48, -51]) (count1632 q) 2 2 (meaning1629 q) (meaning1631 q) (meaning1635 q) hs
  change valuationOf q 1629 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1251 (q : Snake 81) (h : Conditions q) : valuation q 1629 = false ∨ valuation q 1631 = false ∨ valuation q 1635 = true := counterClause1251 (baseVal q)

theorem counterClause1252 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1636)) (countLit q [-52]) (countLit q [-53]) (count1636 q) 1 (meaningNeg53 q) (meaning1636 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1252 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1636 = true := counterClause1252 (baseVal q)

theorem counterClause1253 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1636 = true := by
  have hs : count1636 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1636)) (countLit q [-52]) (countLit q [-53]) (count1636 q) 1 (meaningNeg52 q) (meaning1636 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1253 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1636 = true := counterClause1253 (baseVal q)

theorem counterClause1254 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 53 = true ∨ valuationOf q 1637 = true := by
  have hs : count1636 q = (countLit q [-52]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (1637)) (countLit q [-52]) (countLit q [-53]) (count1636 q) 1 1 (meaningNeg52 q) (meaningNeg53 q) (meaning1637 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1254 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 53 = true ∨ valuation q 1637 = true := counterClause1254 (baseVal q)

theorem counterClause1255 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (1638)) (countLit q [-58]) (countLit q [-60]) (count1638 q) 1 (meaningNeg60 q) (meaning1638 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1255 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1638 = true := counterClause1255 (baseVal q)

theorem counterClause1256 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1638 = true := by
  have hs : count1638 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1638)) (countLit q [-58]) (countLit q [-60]) (count1638 q) 1 (meaningNeg58 q) (meaning1638 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1256 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1638 = true := counterClause1256 (baseVal q)

theorem counterClause1257 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 60 = true ∨ valuationOf q 1639 = true := by
  have hs : count1638 q = (countLit q [-58]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (1639)) (countLit q [-58]) (countLit q [-60]) (count1638 q) 1 1 (meaningNeg58 q) (meaningNeg60 q) (meaning1639 q) hs
  change (! (valuationOf q 58)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1257 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 60 = true ∨ valuation q 1639 = true := counterClause1257 (baseVal q)

theorem counterClause1258 (q : Nat → Bool) : valuationOf q 1638 = false ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58, -60])
  have hm := merge_right (literal (valuationOf q) (1638)) (literal (valuationOf q) (1640)) (countLit q [-56]) (countLit q [-58, -60]) (count1640 q) 1 (meaning1638 q) (meaning1640 q) hs
  change valuationOf q 1638 = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1258 (q : Snake 81) (h : Conditions q) : valuation q 1638 = false ∨ valuation q 1640 = true := counterClause1258 (baseVal q)

theorem counterClause1259 (q : Nat → Bool) : valuationOf q 1639 = false ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58, -60])
  have hm := merge_right (literal (valuationOf q) (1639)) (literal (valuationOf q) (1641)) (countLit q [-56]) (countLit q [-58, -60]) (count1640 q) 2 (meaning1639 q) (meaning1641 q) hs
  change valuationOf q 1639 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1259 (q : Snake 81) (h : Conditions q) : valuation q 1639 = false ∨ valuation q 1641 = true := counterClause1259 (baseVal q)

theorem counterClause1260 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1640 = true := by
  have hs : count1640 q = (countLit q [-56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58, -60])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1640)) (countLit q [-56]) (countLit q [-58, -60]) (count1640 q) 1 (meaningNeg56 q) (meaning1640 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1640 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1260 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1640 = true := counterClause1260 (baseVal q)

theorem counterClause1261 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1638 = false ∨ valuationOf q 1641 = true := by
  have hs : count1640 q = (countLit q [-56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58, -60])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (1638)) (literal (valuationOf q) (1641)) (countLit q [-56]) (countLit q [-58, -60]) (count1640 q) 1 1 (meaningNeg56 q) (meaning1638 q) (meaning1641 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1638 = false ∨ valuationOf q 1641 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1261 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1638 = false ∨ valuation q 1641 = true := counterClause1261 (baseVal q)

theorem counterClause1262 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true := by
  have hs : count1640 q = (countLit q [-56]) + (countLit q [-58, -60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-58, -60])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (1639)) (literal (valuationOf q) (1642)) (countLit q [-56]) (countLit q [-58, -60]) (count1640 q) 1 2 (meaningNeg56 q) (meaning1639 q) (meaning1642 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1639 = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1262 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1639 = false ∨ valuation q 1642 = true := counterClause1262 (baseVal q)

theorem counterClause1263 (q : Nat → Bool) : valuationOf q 1640 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1640)) (literal (valuationOf q) (1643)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 1 (meaning1640 q) (meaning1643 q) hs
  change valuationOf q 1640 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1263 (q : Snake 81) (h : Conditions q) : valuation q 1640 = false ∨ valuation q 1643 = true := counterClause1263 (baseVal q)

theorem counterClause1264 (q : Nat → Bool) : valuationOf q 1641 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1641)) (literal (valuationOf q) (1644)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 2 (meaning1641 q) (meaning1644 q) hs
  change valuationOf q 1641 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1264 (q : Snake 81) (h : Conditions q) : valuation q 1641 = false ∨ valuation q 1644 = true := counterClause1264 (baseVal q)

theorem counterClause1265 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1642)) (literal (valuationOf q) (1645)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 3 (meaning1642 q) (meaning1645 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1265 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1645 = true := counterClause1265 (baseVal q)

theorem counterClause1266 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1643 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_left (literal (valuationOf q) (1636)) (literal (valuationOf q) (1643)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 1 (meaning1636 q) (meaning1643 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1266 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1643 = true := counterClause1266 (baseVal q)

theorem counterClause1267 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1644)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 1 1 (meaning1636 q) (meaning1640 q) (meaning1644 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1267 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1640 = false ∨ valuation q 1644 = true := counterClause1267 (baseVal q)

theorem counterClause1268 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1645)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 1 2 (meaning1636 q) (meaning1641 q) (meaning1645 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1268 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1641 = false ∨ valuation q 1645 = true := counterClause1268 (baseVal q)

theorem counterClause1269 (q : Nat → Bool) : valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1636)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 1 3 (meaning1636 q) (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1636 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1269 (q : Snake 81) (h : Conditions q) : valuation q 1636 = false ∨ valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1269 (baseVal q)

theorem counterClause1270 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1644 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_left (literal (valuationOf q) (1637)) (literal (valuationOf q) (1644)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 2 (meaning1637 q) (meaning1644 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1270 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1644 = true := counterClause1270 (baseVal q)

theorem counterClause1271 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1645 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1640)) (literal (valuationOf q) (1645)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 2 1 (meaning1637 q) (meaning1640 q) (meaning1645 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1640 = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1271 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1640 = false ∨ valuation q 1645 = true := counterClause1271 (baseVal q)

theorem counterClause1272 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1641)) (literal (valuationOf q) (1646)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 2 2 (meaning1637 q) (meaning1641 q) (meaning1646 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1641 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1272 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1641 = false ∨ valuation q 1646 = true := counterClause1272 (baseVal q)

theorem counterClause1273 (q : Nat → Bool) : valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true := by
  have hs : count1643 q = (countLit q [-52, -53]) + (countLit q [-56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -53]) (l₂ := [-56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1637)) (literal (valuationOf q) (1642)) (literal (valuationOf q) (1647)) (countLit q [-52, -53]) (countLit q [-56, -58, -60]) (count1643 q) 2 3 (meaning1637 q) (meaning1642 q) (meaning1647 q) hs
  change valuationOf q 1637 = false ∨ valuationOf q 1642 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1273 (q : Snake 81) (h : Conditions q) : valuation q 1637 = false ∨ valuation q 1642 = false ∨ valuation q 1647 = true := counterClause1273 (baseVal q)

theorem counterClause1274 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1648 = true := by
  have hs : count1648 q = (countLit q [-44, -46, -48, -51]) + (countLit q [-52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -51]) (l₂ := [-52, -53, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1643)) (literal (valuationOf q) (1648)) (countLit q [-44, -46, -48, -51]) (countLit q [-52, -53, -56, -58, -60]) (count1648 q) 1 (meaning1643 q) (meaning1648 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1274 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1648 = true := counterClause1274 (baseVal q)

theorem counterClause1275 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1649 = true := by
  have hs : count1648 q = (countLit q [-44, -46, -48, -51]) + (countLit q [-52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -51]) (l₂ := [-52, -53, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1649)) (countLit q [-44, -46, -48, -51]) (countLit q [-52, -53, -56, -58, -60]) (count1648 q) 2 (meaning1644 q) (meaning1649 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1275 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1649 = true := counterClause1275 (baseVal q)

theorem counterClause1276 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1650 = true := by
  have hs : count1648 q = (countLit q [-44, -46, -48, -51]) + (countLit q [-52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -51]) (l₂ := [-52, -53, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1645)) (literal (valuationOf q) (1650)) (countLit q [-44, -46, -48, -51]) (countLit q [-52, -53, -56, -58, -60]) (count1648 q) 3 (meaning1645 q) (meaning1650 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1276 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1650 = true := counterClause1276 (baseVal q)

theorem counterClause1277 (q : Nat → Bool) : valuationOf q 1646 = false ∨ valuationOf q 1651 = true := by
  have hs : count1648 q = (countLit q [-44, -46, -48, -51]) + (countLit q [-52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -51]) (l₂ := [-52, -53, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1646)) (literal (valuationOf q) (1651)) (countLit q [-44, -46, -48, -51]) (countLit q [-52, -53, -56, -58, -60]) (count1648 q) 4 (meaning1646 q) (meaning1651 q) hs
  change valuationOf q 1646 = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1277 (q : Snake 81) (h : Conditions q) : valuation q 1646 = false ∨ valuation q 1651 = true := counterClause1277 (baseVal q)

theorem counterClause1278 (q : Nat → Bool) : valuationOf q 1647 = false ∨ valuationOf q 1652 = true := by
  have hs : count1648 q = (countLit q [-44, -46, -48, -51]) + (countLit q [-52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -51]) (l₂ := [-52, -53, -56, -58, -60])
  have hm := merge_right (literal (valuationOf q) (1647)) (literal (valuationOf q) (1652)) (countLit q [-44, -46, -48, -51]) (countLit q [-52, -53, -56, -58, -60]) (count1648 q) 5 (meaning1647 q) (meaning1652 q) hs
  change valuationOf q 1647 = false ∨ valuationOf q 1652 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1278 (q : Snake 81) (h : Conditions q) : valuation q 1647 = false ∨ valuation q 1652 = true := counterClause1278 (baseVal q)

theorem counterClause1279 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true := by
  have hs : count1648 q = (countLit q [-44, -46, -48, -51]) + (countLit q [-52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -51]) (l₂ := [-52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1643)) (literal (valuationOf q) (1649)) (countLit q [-44, -46, -48, -51]) (countLit q [-52, -53, -56, -58, -60]) (count1648 q) 1 1 (meaning1632 q) (meaning1643 q) (meaning1649 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1643 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1279 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1643 = false ∨ valuation q 1649 = true := counterClause1279 (baseVal q)

theorem counterClause1280 (q : Nat → Bool) : valuationOf q 1632 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true := by
  have hs : count1648 q = (countLit q [-44, -46, -48, -51]) + (countLit q [-52, -53, -56, -58, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -51]) (l₂ := [-52, -53, -56, -58, -60])
  have hm := merge_two (literal (valuationOf q) (1632)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1650)) (countLit q [-44, -46, -48, -51]) (countLit q [-52, -53, -56, -58, -60]) (count1648 q) 1 2 (meaning1632 q) (meaning1644 q) (meaning1650 q) hs
  change valuationOf q 1632 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1280 (q : Snake 81) (h : Conditions q) : valuation q 1632 = false ∨ valuation q 1644 = false ∨ valuation q 1650 = true := counterClause1280 (baseVal q)

theorem block39 (q : Snake 81) (h : Conditions q) : B112E034.Block39 (valuation q) :=
  ⟨clause1249 q h, clause1250 q h, clause1251 q h, clause1252 q h, clause1253 q h, clause1254 q h, clause1255 q h, clause1256 q h, clause1257 q h, clause1258 q h, clause1259 q h, clause1260 q h, clause1261 q h, clause1262 q h, clause1263 q h, clause1264 q h, clause1265 q h, clause1266 q h, clause1267 q h, clause1268 q h, clause1269 q h, clause1270 q h, clause1271 q h, clause1272 q h, clause1273 q h, clause1274 q h, clause1275 q h, clause1276 q h, clause1277 q h, clause1278 q h, clause1279 q h, clause1280 q h⟩

end
end Snake9.Regrowth.E112034
