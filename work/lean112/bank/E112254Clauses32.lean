import E112254Semantics
import B112E254Inputs
namespace Snake9.Regrowth.E112254
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1570 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_left (literal (valuationOf q) (1559)) (literal (valuationOf q) (1570)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 3 (meaning1559 q) (meaning1570 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1570 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1570 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1571 = true := by
  have hs : count1568 q = (countLit q [-32, -34, -36]) + (countLit q [-38, -41, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36]) (l₂ := [-38, -41, -44, -45])
  have hm := merge_two (literal (valuationOf q) (1559)) (literal (valuationOf q) (1564)) (literal (valuationOf q) (1571)) (countLit q [-32, -34, -36]) (countLit q [-38, -41, -44, -45]) (count1568 q) 3 1 (meaning1559 q) (meaning1564 q) (meaning1571 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1564 = false ∨ valuationOf q 1571 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1564 = false ∨ valuation q 1571 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 1575 = true := by
  have hs : count1575 q = (countLit q [-47]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-47]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (1575)) (countLit q [-47]) (countLit q [-48]) (count1575 q) 1 (meaningNeg48 q) (meaning1575 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 1575 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 1575 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 53 = true ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_right (literal (valuationOf q) (-53)) (literal (valuationOf q) (1577)) (countLit q [-51]) (countLit q [-53]) (count1577 q) 1 (meaningNeg53 q) (meaning1577 q) hs
  change (! (valuationOf q 53)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 53 = true ∨ valuation q 1577 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 1577 = true := by
  have hs : count1577 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_left (literal (valuationOf q) (-51)) (literal (valuationOf q) (1577)) (countLit q [-51]) (countLit q [-53]) (count1577 q) 1 (meaningNeg51 q) (meaning1577 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 1577 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 1577 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 53 = true ∨ valuationOf q 1578 = true := by
  have hs : count1577 q = (countLit q [-51]) + (countLit q [-53]) := List.countP_append (p := literal q) (l₁ := [-51]) (l₂ := [-53])
  have hm := merge_two (literal (valuationOf q) (-51)) (literal (valuationOf q) (-53)) (literal (valuationOf q) (1578)) (countLit q [-51]) (countLit q [-53]) (count1577 q) 1 1 (meaningNeg51 q) (meaningNeg53 q) (meaning1578 q) hs
  change (! (valuationOf q 51)) = false ∨ (! (valuationOf q 53)) = false ∨ valuationOf q 1578 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 53 = true ∨ valuation q 1578 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 1577 = false ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-47, -48]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-47, -48]) (l₂ := [-51, -53])
  have hm := merge_right (literal (valuationOf q) (1577)) (literal (valuationOf q) (1579)) (countLit q [-47, -48]) (countLit q [-51, -53]) (count1579 q) 1 (meaning1577 q) (meaning1579 q) hs
  change valuationOf q 1577 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 1577 = false ∨ valuation q 1579 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 1578 = false ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-47, -48]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-47, -48]) (l₂ := [-51, -53])
  have hm := merge_right (literal (valuationOf q) (1578)) (literal (valuationOf q) (1580)) (countLit q [-47, -48]) (countLit q [-51, -53]) (count1579 q) 2 (meaning1578 q) (meaning1580 q) hs
  change valuationOf q 1578 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 1578 = false ∨ valuation q 1580 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1579 = true := by
  have hs : count1579 q = (countLit q [-47, -48]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-47, -48]) (l₂ := [-51, -53])
  have hm := merge_left (literal (valuationOf q) (1575)) (literal (valuationOf q) (1579)) (countLit q [-47, -48]) (countLit q [-51, -53]) (count1579 q) 1 (meaning1575 q) (meaning1579 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1579 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1579 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true := by
  have hs : count1579 q = (countLit q [-47, -48]) + (countLit q [-51, -53]) := List.countP_append (p := literal q) (l₁ := [-47, -48]) (l₂ := [-51, -53])
  have hm := merge_two (literal (valuationOf q) (1575)) (literal (valuationOf q) (1577)) (literal (valuationOf q) (1580)) (countLit q [-47, -48]) (countLit q [-51, -53]) (count1579 q) 1 1 (meaning1575 q) (meaning1577 q) (meaning1580 q) hs
  change valuationOf q 1575 = false ∨ valuationOf q 1577 = false ∨ valuationOf q 1580 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 1575 = false ∨ valuation q 1577 = false ∨ valuation q 1580 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_right (literal (valuationOf q) (-58)) (literal (valuationOf q) (1583)) (countLit q [-55]) (countLit q [-58]) (count1583 q) 1 (meaningNeg58 q) (meaning1583 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1583 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1583 = true := by
  have hs : count1583 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1583)) (countLit q [-55]) (countLit q [-58]) (count1583 q) 1 (meaningNeg55 q) (meaning1583 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1583 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 58 = true ∨ valuationOf q 1584 = true := by
  have hs : count1583 q = (countLit q [-55]) + (countLit q [-58]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-58])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-58)) (literal (valuationOf q) (1584)) (countLit q [-55]) (countLit q [-58]) (count1583 q) 1 1 (meaningNeg55 q) (meaningNeg58 q) (meaning1584 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 58)) = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 58 = true ∨ valuation q 1584 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_right (literal (valuationOf q) (-62)) (literal (valuationOf q) (1585)) (countLit q [-59]) (countLit q [-62]) (count1585 q) 1 (meaningNeg62 q) (meaning1585 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 1585 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (1585)) (countLit q [-59]) (countLit q [-62]) (count1585 q) 1 (meaningNeg59 q) (meaning1585 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1585 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 62 = true ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-59]) + (countLit q [-62]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-62])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-62)) (literal (valuationOf q) (1586)) (countLit q [-59]) (countLit q [-62]) (count1585 q) 1 1 (meaningNeg59 q) (meaningNeg62 q) (meaning1586 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 62)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 62 = true ∨ valuation q 1586 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-59, -62])
  have hm := merge_right (literal (valuationOf q) (1585)) (literal (valuationOf q) (1587)) (countLit q [-55, -58]) (countLit q [-59, -62]) (count1587 q) 1 (meaning1585 q) (meaning1587 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1587 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-59, -62])
  have hm := merge_right (literal (valuationOf q) (1586)) (literal (valuationOf q) (1588)) (countLit q [-55, -58]) (countLit q [-59, -62]) (count1587 q) 2 (meaning1586 q) (meaning1588 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1588 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-59, -62])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1588)) (countLit q [-55, -58]) (countLit q [-59, -62]) (count1587 q) 1 1 (meaning1583 q) (meaning1585 q) (meaning1588 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1585 = false ∨ valuation q 1588 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-59, -62])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1589)) (countLit q [-55, -58]) (countLit q [-59, -62]) (count1587 q) 1 2 (meaning1583 q) (meaning1586 q) (meaning1589 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1586 = false ∨ valuation q 1589 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-59, -62])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-55, -58]) (countLit q [-59, -62]) (count1587 q) 2 1 (meaning1584 q) (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1585 = false ∨ valuation q 1589 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1590 = true := by
  have hs : count1587 q = (countLit q [-55, -58]) + (countLit q [-59, -62]) := List.countP_append (p := literal q) (l₁ := [-55, -58]) (l₂ := [-59, -62])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1586)) (literal (valuationOf q) (1590)) (countLit q [-55, -58]) (countLit q [-59, -62]) (count1587 q) 2 2 (meaning1584 q) (meaning1586 q) (meaning1590 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1586 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1586 = false ∨ valuation q 1590 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1591 q = (countLit q [-47, -48, -51, -53]) + (countLit q [-55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -51, -53]) (l₂ := [-55, -58, -59, -62])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-47, -48, -51, -53]) (countLit q [-55, -58, -59, -62]) (count1591 q) 1 (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1591 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-47, -48, -51, -53]) + (countLit q [-55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -51, -53]) (l₂ := [-55, -58, -59, -62])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-47, -48, -51, -53]) (countLit q [-55, -58, -59, -62]) (count1591 q) 2 (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1592 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-47, -48, -51, -53]) + (countLit q [-55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -51, -53]) (l₂ := [-55, -58, -59, -62])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-47, -48, -51, -53]) (countLit q [-55, -58, -59, -62]) (count1591 q) 3 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-47, -48, -51, -53]) + (countLit q [-55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -51, -53]) (l₂ := [-55, -58, -59, -62])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-47, -48, -51, -53]) (countLit q [-55, -58, -59, -62]) (count1591 q) 4 (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1594 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true := by
  have hs : count1591 q = (countLit q [-47, -48, -51, -53]) + (countLit q [-55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -51, -53]) (l₂ := [-55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1592)) (countLit q [-47, -48, -51, -53]) (countLit q [-55, -58, -59, -62]) (count1591 q) 1 1 (meaning1579 q) (meaning1587 q) (meaning1592 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1587 = false ∨ valuation q 1592 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-47, -48, -51, -53]) + (countLit q [-55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -51, -53]) (l₂ := [-55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1593)) (countLit q [-47, -48, -51, -53]) (countLit q [-55, -58, -59, -62]) (count1591 q) 1 2 (meaning1579 q) (meaning1588 q) (meaning1593 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1588 = false ∨ valuation q 1593 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true := by
  have hs : count1591 q = (countLit q [-47, -48, -51, -53]) + (countLit q [-55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -51, -53]) (l₂ := [-55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1594)) (countLit q [-47, -48, -51, -53]) (countLit q [-55, -58, -59, -62]) (count1591 q) 1 3 (meaning1579 q) (meaning1589 q) (meaning1594 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1589 = false ∨ valuation q 1594 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 1579 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true := by
  have hs : count1591 q = (countLit q [-47, -48, -51, -53]) + (countLit q [-55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -51, -53]) (l₂ := [-55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1579)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1595)) (countLit q [-47, -48, -51, -53]) (countLit q [-55, -58, -59, -62]) (count1591 q) 1 4 (meaning1579 q) (meaning1590 q) (meaning1595 q) hs
  change valuationOf q 1579 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 1579 = false ∨ valuation q 1590 = false ∨ valuation q 1595 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true := by
  have hs : count1591 q = (countLit q [-47, -48, -51, -53]) + (countLit q [-55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-47, -48, -51, -53]) (l₂ := [-55, -58, -59, -62])
  have hm := merge_two (literal (valuationOf q) (1580)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1593)) (countLit q [-47, -48, -51, -53]) (countLit q [-55, -58, -59, -62]) (count1591 q) 2 1 (meaning1580 q) (meaning1587 q) (meaning1593 q) hs
  change valuationOf q 1580 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 1580 = false ∨ valuation q 1587 = false ∨ valuation q 1593 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1599 = true := by
  have hs : count1599 q = (countLit q [-32, -34, -36, -38, -41, -44, -45]) + (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -38, -41, -44, -45]) (l₂ := [-47, -48, -51, -53, -55, -58, -59, -62])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1599)) (countLit q [-32, -34, -36, -38, -41, -44, -45]) (countLit q [-47, -48, -51, -53, -55, -58, -59, -62]) (count1599 q) 1 (meaning1591 q) (meaning1599 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1599 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E254.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112254
