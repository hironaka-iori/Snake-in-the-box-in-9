import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1548 = true := by
  have hs : count1541 q = (countLit q [-2, -5, -8, -9, -12, -14, -15]) + (countLit q [-18, -19, -22, -25, -27, -29, -31]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -8, -9, -12, -14, -15]) (l₂ := [-18, -19, -22, -25, -27, -29, -31])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1548)) (countLit q [-2, -5, -8, -9, -12, -14, -15]) (countLit q [-18, -19, -22, -25, -27, -29, -31]) (count1541 q) 6 2 (meaning1519 q) (meaning1535 q) (meaning1548 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1535 = false ∨ valuation q 1548 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (1555)) (countLit q [-34]) (countLit q [-36]) (count1555 q) 1 (meaningNeg36 q) (meaning1555 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 1555 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (1555)) (countLit q [-34]) (countLit q [-36]) (count1555 q) 1 (meaningNeg34 q) (meaning1555 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1555 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 36 = true ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (1556)) (countLit q [-34]) (countLit q [-36]) (count1555 q) 1 1 (meaningNeg34 q) (meaningNeg36 q) (meaning1556 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 1556 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (1555)) (literal (valuationOf q) (1557)) (countLit q [-32]) (countLit q [-34, -36]) (count1557 q) 1 (meaning1555 q) (meaning1557 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1557 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (1556)) (literal (valuationOf q) (1558)) (countLit q [-32]) (countLit q [-34, -36]) (count1557 q) 2 (meaning1556 q) (meaning1558 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1558 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1557 = true := by
  have hs : count1557 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1557)) (countLit q [-32]) (countLit q [-34, -36]) (count1557 q) 1 (meaningNeg32 q) (meaning1557 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1557 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1557 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1555 = false ∨ valuationOf q 1558 = true := by
  have hs : count1557 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1558)) (countLit q [-32]) (countLit q [-34, -36]) (count1557 q) 1 1 (meaningNeg32 q) (meaning1555 q) (meaning1558 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1558 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1555 = false ∨ valuation q 1558 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1556 = false ∨ valuationOf q 1559 = true := by
  have hs : count1557 q = (countLit q [-32]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1559)) (countLit q [-32]) (countLit q [-34, -36]) (count1557 q) 1 2 (meaningNeg32 q) (meaning1556 q) (meaning1559 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1556 = false ∨ valuation q 1559 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-38]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (1560)) (countLit q [-38]) (countLit q [-41]) (count1560 q) 1 (meaningNeg41 q) (meaning1560 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 1560 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 1560 = true := by
  have hs : count1560 q = (countLit q [-38]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41])
  have hm := merge_left (literal (valuationOf q) (-38)) (literal (valuationOf q) (1560)) (countLit q [-38]) (countLit q [-41]) (count1560 q) 1 (meaningNeg38 q) (meaning1560 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 1560 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 41 = true ∨ valuationOf q 1561 = true := by
  have hs : count1560 q = (countLit q [-38]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (-41)) (literal (valuationOf q) (1561)) (countLit q [-38]) (countLit q [-41]) (count1560 q) 1 1 (meaningNeg38 q) (meaningNeg41 q) (meaning1561 q) hs
  change (! (valuationOf q 38)) = false ∨ (! (valuationOf q 41)) = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 41 = true ∨ valuation q 1561 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (1562)) (countLit q [-44]) (countLit q [-45]) (count1562 q) 1 (meaningNeg45 q) (meaning1562 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 1562 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 1562 = true := by
  have hs : count1562 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (1562)) (countLit q [-44]) (countLit q [-45]) (count1562 q) 1 (meaningNeg44 q) (meaning1562 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 1562 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 1562 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 45 = true ∨ valuationOf q 1563 = true := by
  have hs : count1562 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (1563)) (countLit q [-44]) (countLit q [-45]) (count1562 q) 1 1 (meaningNeg44 q) (meaningNeg45 q) (meaning1563 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 1563 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 45 = true ∨ valuation q 1563 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 1562 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-38, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-44, -45])
  have hm := merge_right (literal (valuationOf q) (1562)) (literal (valuationOf q) (1564)) (countLit q [-38, -41]) (countLit q [-44, -45]) (count1564 q) 1 (meaning1562 q) (meaning1564 q) hs
  change valuationOf q 1562 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 1562 = false ∨ valuation q 1564 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 1563 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-38, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-44, -45])
  have hm := merge_right (literal (valuationOf q) (1563)) (literal (valuationOf q) (1565)) (countLit q [-38, -41]) (countLit q [-44, -45]) (count1564 q) 2 (meaning1563 q) (meaning1565 q) hs
  change valuationOf q 1563 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 1563 = false ∨ valuation q 1565 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1564 = true := by
  have hs : count1564 q = (countLit q [-38, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-44, -45])
  have hm := merge_left (literal (valuationOf q) (1560)) (literal (valuationOf q) (1564)) (countLit q [-38, -41]) (countLit q [-44, -45]) (count1564 q) 1 (meaning1560 q) (meaning1564 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1564 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1564 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-38, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1565)) (countLit q [-38, -41]) (countLit q [-44, -45]) (count1564 q) 1 1 (meaning1560 q) (meaning1562 q) (meaning1565 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1562 = false ∨ valuation q 1565 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 1560 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-38, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1560)) (literal (valuationOf q) (1563)) (literal (valuationOf q) (1566)) (countLit q [-38, -41]) (countLit q [-44, -45]) (count1564 q) 1 2 (meaning1560 q) (meaning1563 q) (meaning1566 q) hs
  change valuationOf q 1560 = false ∨ valuationOf q 1563 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 1560 = false ∨ valuation q 1563 = false ∨ valuation q 1566 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1565 = true := by
  have hs : count1564 q = (countLit q [-38, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-44, -45])
  have hm := merge_left (literal (valuationOf q) (1561)) (literal (valuationOf q) (1565)) (countLit q [-38, -41]) (countLit q [-44, -45]) (count1564 q) 2 (meaning1561 q) (meaning1565 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1565 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1565 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 1561 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1566 = true := by
  have hs : count1564 q = (countLit q [-38, -41]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-38, -41]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (1561)) (literal (valuationOf q) (1562)) (literal (valuationOf q) (1566)) (countLit q [-38, -41]) (countLit q [-44, -45]) (count1564 q) 2 1 (meaning1561 q) (meaning1562 q) (meaning1566 q) hs
  change valuationOf q 1561 = false ∨ valuationOf q 1562 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 1561 = false ∨ valuation q 1562 = false ∨ valuation q 1566 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 1564 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1564)) (literal (valuationOf q) (1568)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 1 (meaning1564 q) (meaning1568 q) hs
  change valuationOf q 1564 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 1564 = false ∨ valuation q 1568 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 1565 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1565)) (literal (valuationOf q) (1569)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 2 (meaning1565 q) (meaning1569 q) hs
  change valuationOf q 1565 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 1565 = false ∨ valuation q 1569 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 1566 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_right (literal (valuationOf q) (1566)) (literal (valuationOf q) (1570)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 3 (meaning1566 q) (meaning1570 q) hs
  change valuationOf q 1566 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 1566 = false ∨ valuation q 1570 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1568 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_left (literal (valuationOf q) (1557)) (literal (valuationOf q) (1568)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 1 (meaning1557 q) (meaning1568 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1568 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1568 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1569)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 1 1 (meaning1557 q) (meaning1564 q) (meaning1569 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1564 = false ∨ valuation q 1569 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1570)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 1 2 (meaning1557 q) (meaning1565 q) (meaning1570 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1565 = false ∨ valuation q 1570 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 1557 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1571 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1557)) (literal (valuationOf q) (1566)) (literal (valuationOf q) (1571)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 1 3 (meaning1557 q) (meaning1566 q) (meaning1571 q) hs
  change valuationOf q 1557 = false ∨ valuationOf q 1566 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 1557 = false ∨ valuation q 1566 = false ∨ valuation q 1571 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1569 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_left (literal (valuationOf q) (1558)) (literal (valuationOf q) (1569)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 2 (meaning1558 q) (meaning1569 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1569 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1569 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1570)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 2 1 (meaning1558 q) (meaning1564 q) (meaning1570 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1564 = false ∨ valuation q 1570 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 1558 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1558)) (literal (valuationOf q) (1565)) (literal (valuationOf q) (1571)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 2 2 (meaning1558 q) (meaning1565 q) (meaning1571 q) hs
  change valuationOf q 1558 = false ∨ valuationOf q 1565 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 1558 = false ∨ valuation q 1565 = false ∨ valuation q 1571 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E254.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112254
