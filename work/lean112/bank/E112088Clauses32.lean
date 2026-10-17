import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1586)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1585 q) 1 1 (meaning1581 q) (meaning1583 q) (meaning1586 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = false ∨ valuation q 1586 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-94, -95]) + (countLit q [-97, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-97, -100])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1586)) (countLit q [-94, -95]) (countLit q [-97, -100]) (count1585 q) 2 (meaning1582 q) (meaning1586 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1586 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_right (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 1 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_right (literal (valuationOf q) (1586)) (literal (valuationOf q) (1590)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 2 (meaning1586 q) (meaning1590 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1590 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_left (literal (valuationOf q) (1578)) (literal (valuationOf q) (1589)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 1 (meaning1578 q) (meaning1589 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1589 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1590)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 1 1 (meaning1578 q) (meaning1585 q) (meaning1590 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1585 = false ∨ valuation q 1590 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_two (literal (valuationOf q) (1578)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1591)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 1 2 (meaning1578 q) (meaning1586 q) (meaning1591 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1586 = false ∨ valuation q 1591 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_left (literal (valuationOf q) (1579)) (literal (valuationOf q) (1590)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 2 (meaning1579 q) (meaning1590 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1590 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1591)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 2 1 (meaning1579 q) (meaning1585 q) (meaning1591 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1585 = false ∨ valuation q 1591 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1592 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1592)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 2 2 (meaning1579 q) (meaning1586 q) (meaning1592 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1586 = false ∨ valuation q 1592 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_left (literal (valuationOf q) (1580)) (literal (valuationOf q) (1591)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 3 (meaning1580 q) (meaning1591 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1591 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1592 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1592)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 3 1 (meaning1580 q) (meaning1585 q) (meaning1592 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1585 = false ∨ valuation q 1592 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1593 = true := by
  have hs : count1589 q = (countLit q [-88, -90, -92]) + (countLit q [-94, -95, -97, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -90, -92]) (l₂ := [-94, -95, -97, -100])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1593)) (countLit q [-88, -90, -92]) (countLit q [-94, -95, -97, -100]) (count1589 q) 3 2 (meaning1580 q) (meaning1586 q) (meaning1593 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1586 = false ∨ valuation q 1593 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 105 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_right (literal (valuationOf q) (-105)) (literal (valuationOf q) (1596)) (countLit q [-103]) (countLit q [-105]) (count1596 q) 1 (meaningNeg105 q) (meaning1596 q) hs
  change (! (valuationOf q 105)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 105 = true ∨ valuation q 1596 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1596)) (countLit q [-103]) (countLit q [-105]) (count1596 q) 1 (meaningNeg103 q) (meaning1596 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1596 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 105 = true ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-103]) + (countLit q [-105]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-105])
  have hm := merge_two (literal (valuationOf q) (-103)) (literal (valuationOf q) (-105)) (literal (valuationOf q) (1597)) (countLit q [-103]) (countLit q [-105]) (count1596 q) 1 1 (meaningNeg103 q) (meaningNeg105 q) (meaning1597 q) hs
  change (! (valuationOf q 103)) = false ∨ (! (valuationOf q 105)) = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 105 = true ∨ valuation q 1597 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 108 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_right (literal (valuationOf q) (-108)) (literal (valuationOf q) (1598)) (countLit q [-107]) (countLit q [-108]) (count1598 q) 1 (meaningNeg108 q) (meaning1598 q) hs
  change (! (valuationOf q 108)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 108 = true ∨ valuation q 1598 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 107 = true ∨ valuationOf q 1598 = true := by
  have hs : count1598 q = (countLit q [-107]) + (countLit q [-108]) := List.countP_append (p := literal q) (l₁ := [-107]) (l₂ := [-108])
  have hm := merge_left (literal (valuationOf q) (-107)) (literal (valuationOf q) (1598)) (countLit q [-107]) (countLit q [-108]) (count1598 q) 1 (meaningNeg107 q) (meaning1598 q) hs
  change (! (valuationOf q 107)) = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 107 = true ∨ valuation q 1598 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_right (literal (valuationOf q) (1598)) (literal (valuationOf q) (1600)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1600 q) 1 (meaning1598 q) (meaning1600 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1600 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1600 = true := by
  have hs : count1600 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1596)) (literal (valuationOf q) (1600)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1600 q) 1 (meaning1596 q) (meaning1600 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1600 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1596 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_two (literal (valuationOf q) (1596)) (literal (valuationOf q) (1598)) (literal (valuationOf q) (1601)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1600 q) 1 1 (meaning1596 q) (meaning1598 q) (meaning1601 q) hs
  change valuationOf q 1596 = false ∨ valuationOf q 1598 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1596 = false ∨ valuation q 1598 = false ∨ valuation q 1601 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1601 = true := by
  have hs : count1600 q = (countLit q [-103, -105]) + (countLit q [-107, -108]) := List.countP_append (p := literal q) (l₁ := [-103, -105]) (l₂ := [-107, -108])
  have hm := merge_left (literal (valuationOf q) (1597)) (literal (valuationOf q) (1601)) (countLit q [-103, -105]) (countLit q [-107, -108]) (count1600 q) 2 (meaning1597 q) (meaning1601 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1601 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 112 = true ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_right (literal (valuationOf q) (-112)) (literal (valuationOf q) (1604)) (countLit q [-111]) (countLit q [-112]) (count1604 q) 1 (meaningNeg112 q) (meaning1604 q) hs
  change (! (valuationOf q 112)) = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 112 = true ∨ valuation q 1604 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 1604 = true := by
  have hs : count1604 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_left (literal (valuationOf q) (-111)) (literal (valuationOf q) (1604)) (countLit q [-111]) (countLit q [-112]) (count1604 q) 1 (meaningNeg111 q) (meaning1604 q) hs
  change (! (valuationOf q 111)) = false ∨ valuationOf q 1604 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 1604 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 111 = true ∨ valuationOf q 112 = true ∨ valuationOf q 1605 = true := by
  have hs : count1604 q = (countLit q [-111]) + (countLit q [-112]) := List.countP_append (p := literal q) (l₁ := [-111]) (l₂ := [-112])
  have hm := merge_two (literal (valuationOf q) (-111)) (literal (valuationOf q) (-112)) (literal (valuationOf q) (1605)) (countLit q [-111]) (countLit q [-112]) (count1604 q) 1 1 (meaningNeg111 q) (meaningNeg112 q) (meaning1605 q) hs
  change (! (valuationOf q 111)) = false ∨ (! (valuationOf q 112)) = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 111 = true ∨ valuation q 112 = true ∨ valuation q 1605 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 116 = true ∨ valuationOf q 1606 = true := by
  have hs : count1606 q = (countLit q [-113]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-116])
  have hm := merge_right (literal (valuationOf q) (-116)) (literal (valuationOf q) (1606)) (countLit q [-113]) (countLit q [-116]) (count1606 q) 1 (meaningNeg116 q) (meaning1606 q) hs
  change (! (valuationOf q 116)) = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 116 = true ∨ valuation q 1606 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 1606 = true := by
  have hs : count1606 q = (countLit q [-113]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-116])
  have hm := merge_left (literal (valuationOf q) (-113)) (literal (valuationOf q) (1606)) (countLit q [-113]) (countLit q [-116]) (count1606 q) 1 (meaningNeg113 q) (meaning1606 q) hs
  change (! (valuationOf q 113)) = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 1606 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 113 = true ∨ valuationOf q 116 = true ∨ valuationOf q 1607 = true := by
  have hs : count1606 q = (countLit q [-113]) + (countLit q [-116]) := List.countP_append (p := literal q) (l₁ := [-113]) (l₂ := [-116])
  have hm := merge_two (literal (valuationOf q) (-113)) (literal (valuationOf q) (-116)) (literal (valuationOf q) (1607)) (countLit q [-113]) (countLit q [-116]) (count1606 q) 1 1 (meaningNeg113 q) (meaningNeg116 q) (meaning1607 q) hs
  change (! (valuationOf q 113)) = false ∨ (! (valuationOf q 116)) = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 113 = true ∨ valuation q 116 = true ∨ valuation q 1607 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1606 = false ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-111, -112]) + (countLit q [-113, -116]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -116])
  have hm := merge_right (literal (valuationOf q) (1606)) (literal (valuationOf q) (1608)) (countLit q [-111, -112]) (countLit q [-113, -116]) (count1608 q) 1 (meaning1606 q) (meaning1608 q) hs
  change valuationOf q 1606 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1606 = false ∨ valuation q 1608 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1607 = false ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-111, -112]) + (countLit q [-113, -116]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -116])
  have hm := merge_right (literal (valuationOf q) (1607)) (literal (valuationOf q) (1609)) (countLit q [-111, -112]) (countLit q [-113, -116]) (count1608 q) 2 (meaning1607 q) (meaning1609 q) hs
  change valuationOf q 1607 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1607 = false ∨ valuation q 1609 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1608 = true := by
  have hs : count1608 q = (countLit q [-111, -112]) + (countLit q [-113, -116]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -116])
  have hm := merge_left (literal (valuationOf q) (1604)) (literal (valuationOf q) (1608)) (countLit q [-111, -112]) (countLit q [-113, -116]) (count1608 q) 1 (meaning1604 q) (meaning1608 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1608 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1604 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1609 = true := by
  have hs : count1608 q = (countLit q [-111, -112]) + (countLit q [-113, -116]) := List.countP_append (p := literal q) (l₁ := [-111, -112]) (l₂ := [-113, -116])
  have hm := merge_two (literal (valuationOf q) (1604)) (literal (valuationOf q) (1606)) (literal (valuationOf q) (1609)) (countLit q [-111, -112]) (countLit q [-113, -116]) (count1608 q) 1 1 (meaning1604 q) (meaning1606 q) (meaning1609 q) hs
  change valuationOf q 1604 = false ∨ valuationOf q 1606 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1604 = false ∨ valuation q 1606 = false ∨ valuation q 1609 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E088.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112088
