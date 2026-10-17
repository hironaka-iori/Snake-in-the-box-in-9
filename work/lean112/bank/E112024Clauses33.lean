import E112024Semantics
import B112E024Inputs
namespace Snake9.Regrowth.E112024
noncomputable section
local instance blockDec33 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1057 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1599 = true := by
  have hs : count1599 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1599)) (countLit q [-70]) (countLit q [-72]) (count1599 q) 1 (meaningNeg70 q) (meaning1599 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1057 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1599 = true := counterClause1057 (baseVal q)

theorem counterClause1058 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1600 = true := by
  have hs : count1599 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1600)) (countLit q [-70]) (countLit q [-72]) (count1599 q) 1 1 (meaningNeg70 q) (meaningNeg72 q) (meaning1600 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1058 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 72 = true ∨ valuation q 1600 = true := counterClause1058 (baseVal q)

theorem counterClause1059 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_right (literal (valuationOf q) (1599)) (literal (valuationOf q) (1601)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 1 (meaning1599 q) (meaning1601 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1059 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1601 = true := counterClause1059 (baseVal q)

theorem counterClause1060 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1602 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_right (literal (valuationOf q) (1600)) (literal (valuationOf q) (1602)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 2 (meaning1600 q) (meaning1602 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1060 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1602 = true := counterClause1060 (baseVal q)

theorem counterClause1061 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_left (literal (valuationOf q) (1597)) (literal (valuationOf q) (1601)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 1 (meaning1597 q) (meaning1601 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1061 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1601 = true := counterClause1061 (baseVal q)

theorem counterClause1062 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1602)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 1 1 (meaning1597 q) (meaning1599 q) (meaning1602 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1062 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1599 = false ∨ valuation q 1602 = true := counterClause1062 (baseVal q)

theorem counterClause1063 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1603 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1603)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 1 2 (meaning1597 q) (meaning1600 q) (meaning1603 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1063 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1600 = false ∨ valuation q 1603 = true := counterClause1063 (baseVal q)

theorem counterClause1064 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1602 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_left (literal (valuationOf q) (1598)) (literal (valuationOf q) (1602)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 2 (meaning1598 q) (meaning1602 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1064 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1602 = true := counterClause1064 (baseVal q)

theorem counterClause1065 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1603 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1598)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1603)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 2 1 (meaning1598 q) (meaning1599 q) (meaning1603 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1065 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1599 = false ∨ valuation q 1603 = true := counterClause1065 (baseVal q)

theorem counterClause1066 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1066 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1066 (baseVal q)

theorem counterClause1067 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1602)) (literal (valuationOf q) (1606)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 2 (meaning1602 q) (meaning1606 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1067 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1606 = true := counterClause1067 (baseVal q)

theorem counterClause1068 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1607)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 3 (meaning1603 q) (meaning1607 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1068 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1607 = true := counterClause1068 (baseVal q)

theorem counterClause1069 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1593)) (literal (valuationOf q) (1605)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 (meaning1593 q) (meaning1605 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1069 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1605 = true := counterClause1069 (baseVal q)

theorem counterClause1070 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1606)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 1 (meaning1593 q) (meaning1601 q) (meaning1606 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1070 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1601 = false ∨ valuation q 1606 = true := counterClause1070 (baseVal q)

theorem counterClause1071 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1607)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 2 (meaning1593 q) (meaning1602 q) (meaning1607 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1071 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1602 = false ∨ valuation q 1607 = true := counterClause1071 (baseVal q)

theorem counterClause1072 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1608 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1608)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 3 (meaning1593 q) (meaning1603 q) (meaning1608 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1072 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1603 = false ∨ valuation q 1608 = true := counterClause1072 (baseVal q)

theorem counterClause1073 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1594)) (literal (valuationOf q) (1606)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 2 (meaning1594 q) (meaning1606 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1073 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1606 = true := counterClause1073 (baseVal q)

theorem counterClause1074 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1607)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 2 1 (meaning1594 q) (meaning1601 q) (meaning1607 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1074 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1601 = false ∨ valuation q 1607 = true := counterClause1074 (baseVal q)

theorem counterClause1075 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-58, -61, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-58, -61, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1595)) (literal (valuationOf q) (1607)) (countLit q [-58, -61, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 3 (meaning1595 q) (meaning1607 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1075 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1607 = true := counterClause1075 (baseVal q)

theorem counterClause1076 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1613 = true := by
  have hs : count1613 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1613)) (countLit q [-74]) (countLit q [-76]) (count1613 q) 1 (meaningNeg76 q) (meaning1613 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1076 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1613 = true := counterClause1076 (baseVal q)

theorem counterClause1077 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1613 = true := by
  have hs : count1613 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1613)) (countLit q [-74]) (countLit q [-76]) (count1613 q) 1 (meaningNeg74 q) (meaning1613 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1077 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1613 = true := counterClause1077 (baseVal q)

theorem counterClause1078 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1614 = true := by
  have hs : count1613 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1614)) (countLit q [-74]) (countLit q [-76]) (count1613 q) 1 1 (meaningNeg74 q) (meaningNeg76 q) (meaning1614 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1078 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 1614 = true := counterClause1078 (baseVal q)

theorem counterClause1079 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1615)) (countLit q [-77]) (countLit q [-79]) (count1615 q) 1 (meaningNeg77 q) (meaning1615 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1079 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1615 = true := counterClause1079 (baseVal q)

theorem counterClause1080 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1616)) (countLit q [-77]) (countLit q [-79]) (count1615 q) 1 1 (meaningNeg77 q) (meaningNeg79 q) (meaning1616 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1080 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 1616 = true := counterClause1080 (baseVal q)

theorem counterClause1081 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1615)) (literal (valuationOf q) (1617)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 1 (meaning1615 q) (meaning1617 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1081 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1617 = true := counterClause1081 (baseVal q)

theorem counterClause1082 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1616)) (literal (valuationOf q) (1618)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 2 (meaning1616 q) (meaning1618 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1082 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1618 = true := counterClause1082 (baseVal q)

theorem counterClause1083 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1618)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 1 1 (meaning1613 q) (meaning1615 q) (meaning1618 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1083 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1615 = false ∨ valuation q 1618 = true := counterClause1083 (baseVal q)

theorem counterClause1084 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1619 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1619)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 1 2 (meaning1613 q) (meaning1616 q) (meaning1619 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1084 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1616 = false ∨ valuation q 1619 = true := counterClause1084 (baseVal q)

theorem counterClause1085 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1619 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1619)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 2 1 (meaning1614 q) (meaning1615 q) (meaning1619 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1085 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1615 = false ∨ valuation q 1619 = true := counterClause1085 (baseVal q)

theorem counterClause1086 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 2 2 (meaning1614 q) (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1086 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1616 = false ∨ valuation q 1620 = true := counterClause1086 (baseVal q)

theorem counterClause1087 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-81]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1621)) (countLit q [-81]) (countLit q [-85]) (count1621 q) 1 (meaningNeg85 q) (meaning1621 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1087 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1621 = true := counterClause1087 (baseVal q)

theorem counterClause1088 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-81]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1621)) (countLit q [-81]) (countLit q [-85]) (count1621 q) 1 (meaningNeg81 q) (meaning1621 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1088 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1621 = true := counterClause1088 (baseVal q)

theorem block33 (q : Snake 81) (h : Conditions q) : B112E024.Block33 (valuation q) :=
  ⟨clause1057 q h, clause1058 q h, clause1059 q h, clause1060 q h, clause1061 q h, clause1062 q h, clause1063 q h, clause1064 q h, clause1065 q h, clause1066 q h, clause1067 q h, clause1068 q h, clause1069 q h, clause1070 q h, clause1071 q h, clause1072 q h, clause1073 q h, clause1074 q h, clause1075 q h, clause1076 q h, clause1077 q h, clause1078 q h, clause1079 q h, clause1080 q h, clause1081 q h, clause1082 q h, clause1083 q h, clause1084 q h, clause1085 q h, clause1086 q h, clause1087 q h, clause1088 q h⟩

end
end Snake9.Regrowth.E112024
