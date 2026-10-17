import E112110Semantics
import B112E110Inputs
namespace Snake9.Regrowth.E112110
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1600 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1600)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 4 2 (meaning1567 q) (meaning1588 q) (meaning1600 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1600 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1588 = false ∨ valuation q 1600 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1601 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1601)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 4 3 (meaning1567 q) (meaning1589 q) (meaning1601 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1601 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1589 = false ∨ valuation q 1601 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1602 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1602)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 4 4 (meaning1567 q) (meaning1590 q) (meaning1602 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1602 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1590 = false ∨ valuation q 1602 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 1567 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true := by
  have hs : count1595 q = (countLit q [-60, -61, -63, -64, -66, -68, -69]) + (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -63, -64, -66, -68, -69]) (l₂ := [-72, -73, -77, -78, -79, -82, -84, -86])
  have hm := merge_two (literal (valuationOf q) (1567)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1603)) (countLit q [-60, -61, -63, -64, -66, -68, -69]) (countLit q [-72, -73, -77, -78, -79, -82, -84, -86]) (count1595 q) 4 5 (meaning1567 q) (meaning1591 q) (meaning1603 q) hs
  change valuationOf q 1567 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1603 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 1567 = false ∨ valuation q 1591 = false ∨ valuation q 1603 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1610)) (countLit q [-89]) (countLit q [-92]) (count1610 q) 1 (meaningNeg92 q) (meaning1610 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1610 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1610 = true := by
  have hs : count1610 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1610)) (countLit q [-89]) (countLit q [-92]) (count1610 q) 1 (meaningNeg89 q) (meaning1610 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1610 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1610 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 92 = true ∨ valuationOf q 1611 = true := by
  have hs : count1610 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-92)) (literal (valuationOf q) (1611)) (countLit q [-89]) (countLit q [-92]) (count1610 q) 1 1 (meaningNeg89 q) (meaningNeg92 q) (meaning1611 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 92)) = false ∨ valuationOf q 1611 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 92 = true ∨ valuation q 1611 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 1610 = false ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89, -92])
  have hm := merge_right (literal (valuationOf q) (1610)) (literal (valuationOf q) (1612)) (countLit q [-88]) (countLit q [-89, -92]) (count1612 q) 1 (meaning1610 q) (meaning1612 q) hs
  change valuationOf q 1610 = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 1610 = false ∨ valuation q 1612 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 1611 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89, -92])
  have hm := merge_right (literal (valuationOf q) (1611)) (literal (valuationOf q) (1613)) (countLit q [-88]) (countLit q [-89, -92]) (count1612 q) 2 (meaning1611 q) (meaning1613 q) hs
  change valuationOf q 1611 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 1611 = false ∨ valuation q 1613 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1612 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89, -92])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1612)) (countLit q [-88]) (countLit q [-89, -92]) (count1612 q) 1 (meaningNeg88 q) (meaning1612 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1612 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1612 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89, -92])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (1610)) (literal (valuationOf q) (1613)) (countLit q [-88]) (countLit q [-89, -92]) (count1612 q) 1 1 (meaningNeg88 q) (meaning1610 q) (meaning1613 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1610 = false ∨ valuationOf q 1613 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1610 = false ∨ valuation q 1613 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true := by
  have hs : count1612 q = (countLit q [-88]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-89, -92])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (1611)) (literal (valuationOf q) (1614)) (countLit q [-88]) (countLit q [-89, -92]) (count1612 q) 1 2 (meaningNeg88 q) (meaning1611 q) (meaning1614 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1611 = false ∨ valuationOf q 1614 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1611 = false ∨ valuation q 1614 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1615)) (countLit q [-95]) (countLit q [-96]) (count1615 q) 1 (meaningNeg96 q) (meaning1615 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1615 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1615 = true := by
  have hs : count1615 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1615)) (countLit q [-95]) (countLit q [-96]) (count1615 q) 1 (meaningNeg95 q) (meaning1615 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1615 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1615 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1616 = true := by
  have hs : count1615 q = (countLit q [-95]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1616)) (countLit q [-95]) (countLit q [-96]) (count1615 q) 1 1 (meaningNeg95 q) (meaningNeg96 q) (meaning1616 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1616 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 96 = true ∨ valuation q 1616 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1617)) (countLit q [-99]) (countLit q [-100]) (count1617 q) 1 (meaningNeg100 q) (meaning1617 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1617 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1617 = true := by
  have hs : count1617 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1617)) (countLit q [-99]) (countLit q [-100]) (count1617 q) 1 (meaningNeg99 q) (meaning1617 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1617 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1617 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1618 = true := by
  have hs : count1617 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-99)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1618)) (countLit q [-99]) (countLit q [-100]) (count1617 q) 1 1 (meaningNeg99 q) (meaningNeg100 q) (meaning1618 q) hs
  change (! (valuationOf q 99)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1618 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 100 = true ∨ valuation q 1618 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 1617 = false ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-95, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1617)) (literal (valuationOf q) (1619)) (countLit q [-95, -96]) (countLit q [-99, -100]) (count1619 q) 1 (meaning1617 q) (meaning1619 q) hs
  change valuationOf q 1617 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 1617 = false ∨ valuation q 1619 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 1618 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-95, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-99, -100])
  have hm := merge_right (literal (valuationOf q) (1618)) (literal (valuationOf q) (1620)) (countLit q [-95, -96]) (countLit q [-99, -100]) (count1619 q) 2 (meaning1618 q) (meaning1620 q) hs
  change valuationOf q 1618 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 1618 = false ∨ valuation q 1620 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1619 = true := by
  have hs : count1619 q = (countLit q [-95, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-99, -100])
  have hm := merge_left (literal (valuationOf q) (1615)) (literal (valuationOf q) (1619)) (countLit q [-95, -96]) (countLit q [-99, -100]) (count1619 q) 1 (meaning1615 q) (meaning1619 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1619 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1619 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-95, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1620)) (countLit q [-95, -96]) (countLit q [-99, -100]) (count1619 q) 1 1 (meaning1615 q) (meaning1617 q) (meaning1620 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1617 = false ∨ valuation q 1620 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 1615 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1621 = true := by
  have hs : count1619 q = (countLit q [-95, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1615)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1621)) (countLit q [-95, -96]) (countLit q [-99, -100]) (count1619 q) 1 2 (meaning1615 q) (meaning1618 q) (meaning1621 q) hs
  change valuationOf q 1615 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 1615 = false ∨ valuation q 1618 = false ∨ valuation q 1621 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1620 = true := by
  have hs : count1619 q = (countLit q [-95, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-99, -100])
  have hm := merge_left (literal (valuationOf q) (1616)) (literal (valuationOf q) (1620)) (countLit q [-95, -96]) (countLit q [-99, -100]) (count1619 q) 2 (meaning1616 q) (meaning1620 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1620 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1620 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1621 = true := by
  have hs : count1619 q = (countLit q [-95, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1617)) (literal (valuationOf q) (1621)) (countLit q [-95, -96]) (countLit q [-99, -100]) (count1619 q) 2 1 (meaning1616 q) (meaning1617 q) (meaning1621 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1617 = false ∨ valuationOf q 1621 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1617 = false ∨ valuation q 1621 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 1616 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1622 = true := by
  have hs : count1619 q = (countLit q [-95, -96]) + (countLit q [-99, -100]) := List.countP_append (p := literal q) (l₁ := [-95, -96]) (l₂ := [-99, -100])
  have hm := merge_two (literal (valuationOf q) (1616)) (literal (valuationOf q) (1618)) (literal (valuationOf q) (1622)) (countLit q [-95, -96]) (countLit q [-99, -100]) (count1619 q) 2 2 (meaning1616 q) (meaning1618 q) (meaning1622 q) hs
  change valuationOf q 1616 = false ∨ valuationOf q 1618 = false ∨ valuationOf q 1622 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 1616 = false ∨ valuation q 1618 = false ∨ valuation q 1622 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 1619 = false ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1619)) (literal (valuationOf q) (1623)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 1 (meaning1619 q) (meaning1623 q) hs
  change valuationOf q 1619 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 1619 = false ∨ valuation q 1623 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 1620 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1620)) (literal (valuationOf q) (1624)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 2 (meaning1620 q) (meaning1624 q) hs
  change valuationOf q 1620 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 1620 = false ∨ valuation q 1624 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 1621 = false ∨ valuationOf q 1625 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1621)) (literal (valuationOf q) (1625)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 3 (meaning1621 q) (meaning1625 q) hs
  change valuationOf q 1621 = false ∨ valuationOf q 1625 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 1621 = false ∨ valuation q 1625 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 1622 = false ∨ valuationOf q 1626 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_right (literal (valuationOf q) (1622)) (literal (valuationOf q) (1626)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 4 (meaning1622 q) (meaning1626 q) hs
  change valuationOf q 1622 = false ∨ valuationOf q 1626 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 1622 = false ∨ valuation q 1626 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1623 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_left (literal (valuationOf q) (1612)) (literal (valuationOf q) (1623)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 1 (meaning1612 q) (meaning1623 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1623 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1623 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 1612 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true := by
  have hs : count1623 q = (countLit q [-88, -89, -92]) + (countLit q [-95, -96, -99, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -89, -92]) (l₂ := [-95, -96, -99, -100])
  have hm := merge_two (literal (valuationOf q) (1612)) (literal (valuationOf q) (1619)) (literal (valuationOf q) (1624)) (countLit q [-88, -89, -92]) (countLit q [-95, -96, -99, -100]) (count1623 q) 1 1 (meaning1612 q) (meaning1619 q) (meaning1624 q) hs
  change valuationOf q 1612 = false ∨ valuationOf q 1619 = false ∨ valuationOf q 1624 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 1612 = false ∨ valuation q 1619 = false ∨ valuation q 1624 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E110.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112110
