import E112186Semantics
import B112E186Inputs
namespace Snake9.Regrowth.E112186
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1587 = true := by
  have hs : count1584 q = (countLit q [-44, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-44, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (literal (valuationOf q) (1587)) (countLit q [-44, -48]) (countLit q [-50, -51]) (count1584 q) 2 2 (meaning1581 q) (meaning1583 q) (meaning1587 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = false ∨ valuation q 1587 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1588 = true := by
  have hs : count1588 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (1588)) (countLit q [-52]) (countLit q [-54]) (count1588 q) 1 (meaningNeg54 q) (meaning1588 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1588 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 1588 = true := by
  have hs : count1588 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (1588)) (countLit q [-52]) (countLit q [-54]) (count1588 q) 1 (meaningNeg52 q) (meaning1588 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 1588 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 54 = true ∨ valuationOf q 1589 = true := by
  have hs : count1588 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (1589)) (countLit q [-52]) (countLit q [-54]) (count1588 q) 1 1 (meaningNeg52 q) (meaningNeg54 q) (meaning1589 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 1589 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 1590 = true := by
  have hs : count1590 q = (countLit q [-57]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59])
  have hm := merge_right (literal (valuationOf q) (-59)) (literal (valuationOf q) (1590)) (countLit q [-57]) (countLit q [-59]) (count1590 q) 1 (meaningNeg59 q) (meaning1590 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 1590 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 1590 = true := by
  have hs : count1590 q = (countLit q [-57]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (1590)) (countLit q [-57]) (countLit q [-59]) (count1590 q) 1 (meaningNeg57 q) (meaning1590 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 1590 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 59 = true ∨ valuationOf q 1591 = true := by
  have hs : count1590 q = (countLit q [-57]) + (countLit q [-59]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-59])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (-59)) (literal (valuationOf q) (1591)) (countLit q [-57]) (countLit q [-59]) (count1590 q) 1 1 (meaningNeg57 q) (meaningNeg59 q) (meaning1591 q) hs
  change (! (valuationOf q 57)) = false ∨ (! (valuationOf q 59)) = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 59 = true ∨ valuation q 1591 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1592 = true := by
  have hs : count1592 q = (countLit q [-52, -54]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -59])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1592)) (countLit q [-52, -54]) (countLit q [-57, -59]) (count1592 q) 1 (meaning1590 q) (meaning1592 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1592 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-52, -54]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -59])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1593)) (countLit q [-52, -54]) (countLit q [-57, -59]) (count1592 q) 2 (meaning1591 q) (meaning1593 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1593 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1592 q = (countLit q [-52, -54]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -59])
  have hm := merge_left (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-52, -54]) (countLit q [-57, -59]) (count1592 q) 1 (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1592 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-52, -54]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -59])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1593)) (countLit q [-52, -54]) (countLit q [-57, -59]) (count1592 q) 1 1 (meaning1588 q) (meaning1590 q) (meaning1593 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1590 = false ∨ valuation q 1593 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1594 = true := by
  have hs : count1592 q = (countLit q [-52, -54]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -59])
  have hm := merge_two (literal (valuationOf q) (1588)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1594)) (countLit q [-52, -54]) (countLit q [-57, -59]) (count1592 q) 1 2 (meaning1588 q) (meaning1591 q) (meaning1594 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1591 = false ∨ valuation q 1594 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1592 q = (countLit q [-52, -54]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -59])
  have hm := merge_left (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-52, -54]) (countLit q [-57, -59]) (count1592 q) 2 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1592 q = (countLit q [-52, -54]) + (countLit q [-57, -59]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-57, -59])
  have hm := merge_two (literal (valuationOf q) (1589)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-52, -54]) (countLit q [-57, -59]) (count1592 q) 2 1 (meaning1589 q) (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1590 = false ∨ valuation q 1594 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_right (literal (valuationOf q) (1592)) (literal (valuationOf q) (1596)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 1 (meaning1592 q) (meaning1596 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1596 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_right (literal (valuationOf q) (1593)) (literal (valuationOf q) (1597)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 2 (meaning1593 q) (meaning1597 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1597 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1598 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_right (literal (valuationOf q) (1594)) (literal (valuationOf q) (1598)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 3 (meaning1594 q) (meaning1598 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1598 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1596 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1596)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 1 (meaning1584 q) (meaning1596 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1596 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1597)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 1 1 (meaning1584 q) (meaning1592 q) (meaning1597 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1592 = false ∨ valuation q 1597 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1598 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1598)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 1 2 (meaning1584 q) (meaning1593 q) (meaning1598 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1593 = false ∨ valuation q 1598 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1599 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1584)) (literal (valuationOf q) (1594)) (literal (valuationOf q) (1599)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 1 3 (meaning1584 q) (meaning1594 q) (meaning1599 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1594 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1594 = false ∨ valuation q 1599 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1597 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1597)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 2 (meaning1585 q) (meaning1597 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1597 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1598 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1598)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 2 1 (meaning1585 q) (meaning1592 q) (meaning1598 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1592 = false ∨ valuation q 1598 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1599 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1599)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 2 2 (meaning1585 q) (meaning1593 q) (meaning1599 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1593 = false ∨ valuation q 1599 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1598 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1598)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 3 (meaning1586 q) (meaning1598 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1598 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1598 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1599 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1599)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 3 1 (meaning1586 q) (meaning1592 q) (meaning1599 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1592 = false ∨ valuation q 1599 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1600 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1593)) (literal (valuationOf q) (1600)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 3 2 (meaning1586 q) (meaning1593 q) (meaning1600 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1593 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1593 = false ∨ valuation q 1600 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1599 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_left (literal (valuationOf q) (1587)) (literal (valuationOf q) (1599)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 4 (meaning1587 q) (meaning1599 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1599 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1600 = true := by
  have hs : count1596 q = (countLit q [-44, -48, -50, -51]) + (countLit q [-52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-44, -48, -50, -51]) (l₂ := [-52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1587)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1600)) (countLit q [-44, -48, -50, -51]) (countLit q [-52, -54, -57, -59]) (count1596 q) 4 1 (meaning1587 q) (meaning1592 q) (meaning1600 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1592 = false ∨ valuation q 1600 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1608 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1608)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 1 4 (meaning1572 q) (meaning1599 q) (meaning1608 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1599 = false ∨ valuation q 1608 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1572 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1609 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1572)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1609)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 1 5 (meaning1572 q) (meaning1600 q) (meaning1609 q) hs
  change valuationOf q 1572 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1609 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1572 = false ∨ valuation q 1600 = false ∨ valuation q 1609 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1573 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1606 = true := by
  have hs : count1604 q = (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) + (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-31, -33, -34, -36, -37, -41, -42, -43]) (l₂ := [-44, -48, -50, -51, -52, -54, -57, -59])
  have hm := merge_two (literal (valuationOf q) (1573)) (literal (valuationOf q) (1596)) (literal (valuationOf q) (1606)) (countLit q [-31, -33, -34, -36, -37, -41, -42, -43]) (countLit q [-44, -48, -50, -51, -52, -54, -57, -59]) (count1604 q) 2 1 (meaning1573 q) (meaning1596 q) (meaning1606 q) hs
  change valuationOf q 1573 = false ∨ valuationOf q 1596 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1573 = false ∨ valuation q 1596 = false ∨ valuation q 1606 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E186.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112186
