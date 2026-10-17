import E112026Semantics
import B112E026Inputs
namespace Snake9.Regrowth.E112026
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1599 = true := by
  have hs : count1599 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-70)) (literal (valuationOf q) (1599)) (countLit q [-70]) (countLit q [-72]) (count1599 q) 1 (meaningNeg70 q) (meaning1599 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1599 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1599 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 72 = true ∨ valuationOf q 1600 = true := by
  have hs : count1599 q = (countLit q [-70]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-70]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-70)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (1600)) (countLit q [-70]) (countLit q [-72]) (count1599 q) 1 1 (meaningNeg70 q) (meaningNeg72 q) (meaning1600 q) hs
  change (! (valuationOf q 70)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 72 = true ∨ valuation q 1600 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1599 = false ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_right (literal (valuationOf q) (1599)) (literal (valuationOf q) (1601)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 1 (meaning1599 q) (meaning1601 q) hs
  change valuationOf q 1599 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1599 = false ∨ valuation q 1601 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1600 = false ∨ valuationOf q 1602 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_right (literal (valuationOf q) (1600)) (literal (valuationOf q) (1602)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 2 (meaning1600 q) (meaning1602 q) hs
  change valuationOf q 1600 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1600 = false ∨ valuation q 1602 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1601 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_left (literal (valuationOf q) (1597)) (literal (valuationOf q) (1601)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 1 (meaning1597 q) (meaning1601 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1601 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1599)) (literal (valuationOf q) (1602)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 1 1 (meaning1597 q) (meaning1599 q) (meaning1602 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1599 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1599 = false ∨ valuation q 1602 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 1597 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1603 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_two (literal (valuationOf q) (1597)) (literal (valuationOf q) (1600)) (literal (valuationOf q) (1603)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 1 2 (meaning1597 q) (meaning1600 q) (meaning1603 q) hs
  change valuationOf q 1597 = false ∨ valuationOf q 1600 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 1597 = false ∨ valuation q 1600 = false ∨ valuation q 1603 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1598 = false ∨ valuationOf q 1602 = true := by
  have hs : count1601 q = (countLit q [-67, -69]) + (countLit q [-70, -72]) := List.countP_append (p := literal q) (l₁ := [-67, -69]) (l₂ := [-70, -72])
  have hm := merge_left (literal (valuationOf q) (1598)) (literal (valuationOf q) (1602)) (countLit q [-67, -69]) (countLit q [-70, -72]) (count1601 q) 2 (meaning1598 q) (meaning1602 q) hs
  change valuationOf q 1598 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1598 = false ∨ valuation q 1602 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1601 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1601)) (literal (valuationOf q) (1605)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 (meaning1601 q) (meaning1605 q) hs
  change valuationOf q 1601 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1601 = false ∨ valuation q 1605 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 1602 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1602)) (literal (valuationOf q) (1606)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 2 (meaning1602 q) (meaning1606 q) hs
  change valuationOf q 1602 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 1602 = false ∨ valuation q 1606 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 1603 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_right (literal (valuationOf q) (1603)) (literal (valuationOf q) (1607)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 3 (meaning1603 q) (meaning1607 q) hs
  change valuationOf q 1603 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 1603 = false ∨ valuation q 1607 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1605 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1593)) (literal (valuationOf q) (1605)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 (meaning1593 q) (meaning1605 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1605 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1605 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1606)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 1 (meaning1593 q) (meaning1601 q) (meaning1606 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1601 = false ∨ valuation q 1606 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1607)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 2 (meaning1593 q) (meaning1602 q) (meaning1607 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1602 = false ∨ valuation q 1607 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 1593 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1608 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1593)) (literal (valuationOf q) (1603)) (literal (valuationOf q) (1608)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 1 3 (meaning1593 q) (meaning1603 q) (meaning1608 q) hs
  change valuationOf q 1593 = false ∨ valuationOf q 1603 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 1593 = false ∨ valuation q 1603 = false ∨ valuation q 1608 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1606 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1594)) (literal (valuationOf q) (1606)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 2 (meaning1594 q) (meaning1606 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1606 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1606 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1607)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 2 1 (meaning1594 q) (meaning1601 q) (meaning1607 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1601 = false ∨ valuation q 1607 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 1594 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1608 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1594)) (literal (valuationOf q) (1602)) (literal (valuationOf q) (1608)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 2 2 (meaning1594 q) (meaning1602 q) (meaning1608 q) hs
  change valuationOf q 1594 = false ∨ valuationOf q 1602 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 1594 = false ∨ valuation q 1602 = false ∨ valuation q 1608 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1607 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_left (literal (valuationOf q) (1595)) (literal (valuationOf q) (1607)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 3 (meaning1595 q) (meaning1607 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1607 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1607 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1595 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1608 = true := by
  have hs : count1605 q = (countLit q [-57, -60, -62, -63]) + (countLit q [-67, -69, -70, -72]) := List.countP_append (p := literal q) (l₁ := [-57, -60, -62, -63]) (l₂ := [-67, -69, -70, -72])
  have hm := merge_two (literal (valuationOf q) (1595)) (literal (valuationOf q) (1601)) (literal (valuationOf q) (1608)) (countLit q [-57, -60, -62, -63]) (countLit q [-67, -69, -70, -72]) (count1605 q) 3 1 (meaning1595 q) (meaning1601 q) (meaning1608 q) hs
  change valuationOf q 1595 = false ∨ valuationOf q 1601 = false ∨ valuationOf q 1608 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1595 = false ∨ valuation q 1601 = false ∨ valuation q 1608 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1613 = true := by
  have hs : count1613 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1613)) (countLit q [-74]) (countLit q [-76]) (count1613 q) 1 (meaningNeg76 q) (meaning1613 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1613 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1613 = true := by
  have hs : count1613 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1613)) (countLit q [-74]) (countLit q [-76]) (count1613 q) 1 (meaningNeg74 q) (meaning1613 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1613 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 76 = true ∨ valuationOf q 1614 = true := by
  have hs : count1613 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_two (literal (valuationOf q) (-74)) (literal (valuationOf q) (-76)) (literal (valuationOf q) (1614)) (countLit q [-74]) (countLit q [-76]) (count1613 q) 1 1 (meaningNeg74 q) (meaningNeg76 q) (meaning1614 q) hs
  change (! (valuationOf q 74)) = false ∨ (! (valuationOf q 76)) = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 76 = true ∨ valuation q 1614 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1615)) (countLit q [-77]) (countLit q [-79]) (count1615 q) 1 (meaningNeg77 q) (meaning1615 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1615 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-77]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-77)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1616)) (countLit q [-77]) (countLit q [-79]) (count1615 q) 1 1 (meaningNeg77 q) (meaningNeg79 q) (meaning1616 q) hs
  change (! (valuationOf q 77)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 79 = true ∨ valuation q 1616 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1615)) (literal (valuationOf q) (1617)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 1 (meaning1615 q) (meaning1617 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1617 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_right (literal (valuationOf q) (1616)) (literal (valuationOf q) (1618)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 2 (meaning1616 q) (meaning1618 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1618 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1618)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 1 1 (meaning1613 q) (meaning1615 q) (meaning1618 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1615 = false ∨ valuation q 1618 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1613 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1619 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1613)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1619)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 1 2 (meaning1613 q) (meaning1616 q) (meaning1619 q) hs
  change valuationOf q 1613 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1613 = false ∨ valuation q 1616 = false ∨ valuation q 1619 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1619 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1615)) (literal (valuationOf q) (1619)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 2 1 (meaning1614 q) (meaning1615 q) (meaning1619 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1615 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1615 = false ∨ valuation q 1619 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1614 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1617 q = (countLit q [-74, -76]) + (countLit q [-77, -79]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -79])
  have hm := merge_two (literal (valuationOf q) (1614)) (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-74, -76]) (countLit q [-77, -79]) (count1617 q) 2 2 (meaning1614 q) (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1614 = false ∨ valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1614 = false ∨ valuation q 1616 = false ∨ valuation q 1620 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1621 = true := by
  have hs : count1621 q = (countLit q [-81]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1621)) (countLit q [-81]) (countLit q [-85]) (count1621 q) 1 (meaningNeg85 q) (meaning1621 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1621 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E026.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112026
