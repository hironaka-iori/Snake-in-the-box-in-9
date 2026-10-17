import E112050Semantics
import B112E050Inputs
namespace Snake9.Regrowth.E112050
noncomputable section
local instance blockDec38 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1217 (q : Nat → Bool) : valuationOf q 1633 = false ∨ valuationOf q 1637 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_right (literal (valuationOf q) (1633)) (literal (valuationOf q) (1637)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 4 (meaning1633 q) (meaning1637 q) hs
  change valuationOf q 1633 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1217 (q : Snake 81) (h : Conditions q) : valuation q 1633 = false ∨ valuation q 1637 = true := counterClause1217 (baseVal q)

theorem counterClause1218 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1634 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1622)) (literal (valuationOf q) (1634)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 1 (meaning1622 q) (meaning1634 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1634 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1218 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1634 = true := counterClause1218 (baseVal q)

theorem counterClause1219 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1635)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 1 1 (meaning1622 q) (meaning1630 q) (meaning1635 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1219 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1630 = false ∨ valuation q 1635 = true := counterClause1219 (baseVal q)

theorem counterClause1220 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1636)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 1 2 (meaning1622 q) (meaning1631 q) (meaning1636 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1220 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1631 = false ∨ valuation q 1636 = true := counterClause1220 (baseVal q)

theorem counterClause1221 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1637 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1622)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1637)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 1 3 (meaning1622 q) (meaning1632 q) (meaning1637 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1221 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1632 = false ∨ valuation q 1637 = true := counterClause1221 (baseVal q)

theorem counterClause1222 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1635 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1623)) (literal (valuationOf q) (1635)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 2 (meaning1623 q) (meaning1635 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1635 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1222 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1635 = true := counterClause1222 (baseVal q)

theorem counterClause1223 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1636)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 2 1 (meaning1623 q) (meaning1630 q) (meaning1636 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1223 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1630 = false ∨ valuation q 1636 = true := counterClause1223 (baseVal q)

theorem counterClause1224 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1637 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1637)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 2 2 (meaning1623 q) (meaning1631 q) (meaning1637 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1224 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1631 = false ∨ valuation q 1637 = true := counterClause1224 (baseVal q)

theorem counterClause1225 (q : Nat → Bool) : valuationOf q 1623 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1638 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1623)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1638)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 2 3 (meaning1623 q) (meaning1632 q) (meaning1638 q) hs
  change valuationOf q 1623 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1225 (q : Snake 81) (h : Conditions q) : valuation q 1623 = false ∨ valuation q 1632 = false ∨ valuation q 1638 = true := counterClause1225 (baseVal q)

theorem counterClause1226 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1636 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1624)) (literal (valuationOf q) (1636)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 3 (meaning1624 q) (meaning1636 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1636 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1226 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1636 = true := counterClause1226 (baseVal q)

theorem counterClause1227 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1637 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1637)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 3 1 (meaning1624 q) (meaning1630 q) (meaning1637 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1227 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1630 = false ∨ valuation q 1637 = true := counterClause1227 (baseVal q)

theorem counterClause1228 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1638 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1631)) (literal (valuationOf q) (1638)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 3 2 (meaning1624 q) (meaning1631 q) (meaning1638 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1631 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1228 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1631 = false ∨ valuation q 1638 = true := counterClause1228 (baseVal q)

theorem counterClause1229 (q : Nat → Bool) : valuationOf q 1624 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1639 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1624)) (literal (valuationOf q) (1632)) (literal (valuationOf q) (1639)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 3 3 (meaning1624 q) (meaning1632 q) (meaning1639 q) hs
  change valuationOf q 1624 = false ∨ valuationOf q 1632 = false ∨ valuationOf q 1639 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1229 (q : Snake 81) (h : Conditions q) : valuation q 1624 = false ∨ valuation q 1632 = false ∨ valuation q 1639 = true := counterClause1229 (baseVal q)

theorem counterClause1230 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1637 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_left (literal (valuationOf q) (1625)) (literal (valuationOf q) (1637)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 4 (meaning1625 q) (meaning1637 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1637 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1230 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1637 = true := counterClause1230 (baseVal q)

theorem counterClause1231 (q : Nat → Bool) : valuationOf q 1625 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1638 = true := by
  have hs : count1634 q = (countLit q [-30, -33, -35, -36]) + (countLit q [-39, -42, -43, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -33, -35, -36]) (l₂ := [-39, -42, -43, -45])
  have hm := merge_two (literal (valuationOf q) (1625)) (literal (valuationOf q) (1630)) (literal (valuationOf q) (1638)) (countLit q [-30, -33, -35, -36]) (countLit q [-39, -42, -43, -45]) (count1634 q) 4 1 (meaning1625 q) (meaning1630 q) (meaning1638 q) hs
  change valuationOf q 1625 = false ∨ valuationOf q 1630 = false ∨ valuationOf q 1638 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1231 (q : Snake 81) (h : Conditions q) : valuation q 1625 = false ∨ valuation q 1630 = false ∨ valuation q 1638 = true := counterClause1231 (baseVal q)

theorem counterClause1232 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-46]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (1642)) (countLit q [-46]) (countLit q [-51]) (count1642 q) 1 (meaningNeg51 q) (meaning1642 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1232 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1642 = true := counterClause1232 (baseVal q)

theorem counterClause1233 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 1642 = true := by
  have hs : count1642 q = (countLit q [-46]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (1642)) (countLit q [-46]) (countLit q [-51]) (count1642 q) 1 (meaningNeg46 q) (meaning1642 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 1642 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1233 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 1642 = true := counterClause1233 (baseVal q)

theorem counterClause1234 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 51 = true ∨ valuationOf q 1643 = true := by
  have hs : count1642 q = (countLit q [-46]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (1643)) (countLit q [-46]) (countLit q [-51]) (count1642 q) 1 1 (meaningNeg46 q) (meaningNeg51 q) (meaning1643 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 1643 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1234 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 51 = true ∨ valuation q 1643 = true := counterClause1234 (baseVal q)

theorem counterClause1235 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1644 = true := by
  have hs : count1644 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1644)) (countLit q [-53]) (countLit q [-54]) (count1644 q) 1 (meaningNeg54 q) (meaning1644 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1235 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1644 = true := counterClause1235 (baseVal q)

theorem counterClause1236 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1644 = true := by
  have hs : count1644 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-53)) (literal (valuationOf q) (1644)) (countLit q [-53]) (countLit q [-54]) (count1644 q) 1 (meaningNeg53 q) (meaning1644 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1644 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1236 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1644 = true := counterClause1236 (baseVal q)

theorem counterClause1237 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1645 = true := by
  have hs : count1644 q = (countLit q [-53]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-53]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-53)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1645)) (countLit q [-53]) (countLit q [-54]) (count1644 q) 1 1 (meaningNeg53 q) (meaningNeg54 q) (meaning1645 q) hs
  change (! (valuationOf q 53)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1645 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1237 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 54 = true ∨ valuation q 1645 = true := counterClause1237 (baseVal q)

theorem counterClause1238 (q : Nat → Bool) : valuationOf q 1644 = false ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_right (literal (valuationOf q) (1644)) (literal (valuationOf q) (1646)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1646 q) 1 (meaning1644 q) (meaning1646 q) hs
  change valuationOf q 1644 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1238 (q : Snake 81) (h : Conditions q) : valuation q 1644 = false ∨ valuation q 1646 = true := counterClause1238 (baseVal q)

theorem counterClause1239 (q : Nat → Bool) : valuationOf q 1645 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_right (literal (valuationOf q) (1645)) (literal (valuationOf q) (1647)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1646 q) 2 (meaning1645 q) (meaning1647 q) hs
  change valuationOf q 1645 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1239 (q : Snake 81) (h : Conditions q) : valuation q 1645 = false ∨ valuation q 1647 = true := counterClause1239 (baseVal q)

theorem counterClause1240 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1646 = true := by
  have hs : count1646 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_left (literal (valuationOf q) (1642)) (literal (valuationOf q) (1646)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1646 q) 1 (meaning1642 q) (meaning1646 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1646 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1240 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1646 = true := counterClause1240 (baseVal q)

theorem counterClause1241 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1647)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1646 q) 1 1 (meaning1642 q) (meaning1644 q) (meaning1647 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1241 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1644 = false ∨ valuation q 1647 = true := counterClause1241 (baseVal q)

theorem counterClause1242 (q : Nat → Bool) : valuationOf q 1642 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1642)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1648)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1646 q) 1 2 (meaning1642 q) (meaning1645 q) (meaning1648 q) hs
  change valuationOf q 1642 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1242 (q : Snake 81) (h : Conditions q) : valuation q 1642 = false ∨ valuation q 1645 = false ∨ valuation q 1648 = true := counterClause1242 (baseVal q)

theorem counterClause1243 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1647 = true := by
  have hs : count1646 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_left (literal (valuationOf q) (1643)) (literal (valuationOf q) (1647)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1646 q) 2 (meaning1643 q) (meaning1647 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1647 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1243 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1647 = true := counterClause1243 (baseVal q)

theorem counterClause1244 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1648 = true := by
  have hs : count1646 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1644)) (literal (valuationOf q) (1648)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1646 q) 2 1 (meaning1643 q) (meaning1644 q) (meaning1648 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1644 = false ∨ valuationOf q 1648 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1244 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1644 = false ∨ valuation q 1648 = true := counterClause1244 (baseVal q)

theorem counterClause1245 (q : Nat → Bool) : valuationOf q 1643 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1649 = true := by
  have hs : count1646 q = (countLit q [-46, -51]) + (countLit q [-53, -54]) := List.countP_append (p := literal q) (l₁ := [-46, -51]) (l₂ := [-53, -54])
  have hm := merge_two (literal (valuationOf q) (1643)) (literal (valuationOf q) (1645)) (literal (valuationOf q) (1649)) (countLit q [-46, -51]) (countLit q [-53, -54]) (count1646 q) 2 2 (meaning1643 q) (meaning1645 q) (meaning1649 q) hs
  change valuationOf q 1643 = false ∨ valuationOf q 1645 = false ∨ valuationOf q 1649 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1245 (q : Snake 81) (h : Conditions q) : valuation q 1643 = false ∨ valuation q 1645 = false ∨ valuation q 1649 = true := counterClause1245 (baseVal q)

theorem counterClause1246 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-56]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (1650)) (countLit q [-56]) (countLit q [-60]) (count1650 q) 1 (meaningNeg60 q) (meaning1650 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1246 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1650 = true := counterClause1246 (baseVal q)

theorem counterClause1247 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 1650 = true := by
  have hs : count1650 q = (countLit q [-56]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-56)) (literal (valuationOf q) (1650)) (countLit q [-56]) (countLit q [-60]) (count1650 q) 1 (meaningNeg56 q) (meaning1650 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 1650 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1247 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 1650 = true := counterClause1247 (baseVal q)

theorem counterClause1248 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 60 = true ∨ valuationOf q 1651 = true := by
  have hs : count1650 q = (countLit q [-56]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-56]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-56)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (1651)) (countLit q [-56]) (countLit q [-60]) (count1650 q) 1 1 (meaningNeg56 q) (meaningNeg60 q) (meaning1651 q) hs
  change (! (valuationOf q 56)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 1651 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1248 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 60 = true ∨ valuation q 1651 = true := counterClause1248 (baseVal q)

theorem block38 (q : Snake 81) (h : Conditions q) : B112E050.Block38 (valuation q) :=
  ⟨clause1217 q h, clause1218 q h, clause1219 q h, clause1220 q h, clause1221 q h, clause1222 q h, clause1223 q h, clause1224 q h, clause1225 q h, clause1226 q h, clause1227 q h, clause1228 q h, clause1229 q h, clause1230 q h, clause1231 q h, clause1232 q h, clause1233 q h, clause1234 q h, clause1235 q h, clause1236 q h, clause1237 q h, clause1238 q h, clause1239 q h, clause1240 q h, clause1241 q h, clause1242 q h, clause1243 q h, clause1244 q h, clause1245 q h, clause1246 q h, clause1247 q h, clause1248 q h⟩

end
end Snake9.Regrowth.E112050
