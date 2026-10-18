import E112120Semantics
import B112E120Inputs
namespace Snake9.Regrowth.E112120
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1581 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-88]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91, -92])
  have hm := merge_right (literal (valuationOf q) (1581)) (literal (valuationOf q) (1583)) (countLit q [-88]) (countLit q [-91, -92]) (count1582 q) 2 (meaning1581 q) (meaning1583 q) hs
  change valuationOf q 1581 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1581 = false ∨ valuation q 1583 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1582 = true := by
  have hs : count1582 q = (countLit q [-88]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91, -92])
  have hm := merge_left (literal (valuationOf q) (-88)) (literal (valuationOf q) (1582)) (countLit q [-88]) (countLit q [-91, -92]) (count1582 q) 1 (meaningNeg88 q) (meaning1582 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1582 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1582 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true := by
  have hs : count1582 q = (countLit q [-88]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91, -92])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (1580)) (literal (valuationOf q) (1583)) (countLit q [-88]) (countLit q [-91, -92]) (count1582 q) 1 1 (meaningNeg88 q) (meaning1580 q) (meaning1583 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1580 = false ∨ valuationOf q 1583 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1580 = false ∨ valuation q 1583 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 88 = true ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true := by
  have hs : count1582 q = (countLit q [-88]) + (countLit q [-91, -92]) := List.countP_append (p := literal q) (l₁ := [-88]) (l₂ := [-91, -92])
  have hm := merge_two (literal (valuationOf q) (-88)) (literal (valuationOf q) (1581)) (literal (valuationOf q) (1584)) (countLit q [-88]) (countLit q [-91, -92]) (count1582 q) 1 2 (meaningNeg88 q) (meaning1581 q) (meaning1584 q) hs
  change (! (valuationOf q 88)) = false ∨ valuationOf q 1581 = false ∨ valuationOf q 1584 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 88 = true ∨ valuation q 1581 = false ∨ valuation q 1584 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1585)) (countLit q [-94]) (countLit q [-95]) (count1585 q) 1 (meaningNeg95 q) (meaning1585 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1585 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1585 = true := by
  have hs : count1585 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1585)) (countLit q [-94]) (countLit q [-95]) (count1585 q) 1 (meaningNeg94 q) (meaning1585 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1585 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1585 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 95 = true ∨ valuationOf q 1586 = true := by
  have hs : count1585 q = (countLit q [-94]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (-95)) (literal (valuationOf q) (1586)) (countLit q [-94]) (countLit q [-95]) (count1585 q) 1 1 (meaningNeg94 q) (meaningNeg95 q) (meaning1586 q) hs
  change (! (valuationOf q 94)) = false ∨ (! (valuationOf q 95)) = false ∨ valuationOf q 1586 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 95 = true ∨ valuation q 1586 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-96]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1587)) (countLit q [-96]) (countLit q [-100]) (count1587 q) 1 (meaningNeg100 q) (meaning1587 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1587 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1587 = true := by
  have hs : count1587 q = (countLit q [-96]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1587)) (countLit q [-96]) (countLit q [-100]) (count1587 q) 1 (meaningNeg96 q) (meaning1587 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1587 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1587 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 100 = true ∨ valuationOf q 1588 = true := by
  have hs : count1587 q = (countLit q [-96]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-100])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-100)) (literal (valuationOf q) (1588)) (countLit q [-96]) (countLit q [-100]) (count1587 q) 1 1 (meaningNeg96 q) (meaningNeg100 q) (meaning1588 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 100)) = false ∨ valuationOf q 1588 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 100 = true ∨ valuation q 1588 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1587 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-94, -95]) + (countLit q [-96, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-96, -100])
  have hm := merge_right (literal (valuationOf q) (1587)) (literal (valuationOf q) (1589)) (countLit q [-94, -95]) (countLit q [-96, -100]) (count1589 q) 1 (meaning1587 q) (meaning1589 q) hs
  change valuationOf q 1587 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1587 = false ∨ valuation q 1589 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1588 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-94, -95]) + (countLit q [-96, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-96, -100])
  have hm := merge_right (literal (valuationOf q) (1588)) (literal (valuationOf q) (1590)) (countLit q [-94, -95]) (countLit q [-96, -100]) (count1589 q) 2 (meaning1588 q) (meaning1590 q) hs
  change valuationOf q 1588 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1588 = false ∨ valuation q 1590 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1589 = true := by
  have hs : count1589 q = (countLit q [-94, -95]) + (countLit q [-96, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-96, -100])
  have hm := merge_left (literal (valuationOf q) (1585)) (literal (valuationOf q) (1589)) (countLit q [-94, -95]) (countLit q [-96, -100]) (count1589 q) 1 (meaning1585 q) (meaning1589 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1589 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1589 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-94, -95]) + (countLit q [-96, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-96, -100])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1590)) (countLit q [-94, -95]) (countLit q [-96, -100]) (count1589 q) 1 1 (meaning1585 q) (meaning1587 q) (meaning1590 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1587 = false ∨ valuation q 1590 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1585 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-94, -95]) + (countLit q [-96, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-96, -100])
  have hm := merge_two (literal (valuationOf q) (1585)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1591)) (countLit q [-94, -95]) (countLit q [-96, -100]) (count1589 q) 1 2 (meaning1585 q) (meaning1588 q) (meaning1591 q) hs
  change valuationOf q 1585 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1585 = false ∨ valuation q 1588 = false ∨ valuation q 1591 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1590 = true := by
  have hs : count1589 q = (countLit q [-94, -95]) + (countLit q [-96, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-96, -100])
  have hm := merge_left (literal (valuationOf q) (1586)) (literal (valuationOf q) (1590)) (countLit q [-94, -95]) (countLit q [-96, -100]) (count1589 q) 2 (meaning1586 q) (meaning1590 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1590 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1590 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1591 = true := by
  have hs : count1589 q = (countLit q [-94, -95]) + (countLit q [-96, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-96, -100])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1587)) (literal (valuationOf q) (1591)) (countLit q [-94, -95]) (countLit q [-96, -100]) (count1589 q) 2 1 (meaning1586 q) (meaning1587 q) (meaning1591 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1587 = false ∨ valuationOf q 1591 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1587 = false ∨ valuation q 1591 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1586 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1592 = true := by
  have hs : count1589 q = (countLit q [-94, -95]) + (countLit q [-96, -100]) := List.countP_append (p := literal q) (l₁ := [-94, -95]) (l₂ := [-96, -100])
  have hm := merge_two (literal (valuationOf q) (1586)) (literal (valuationOf q) (1588)) (literal (valuationOf q) (1592)) (countLit q [-94, -95]) (countLit q [-96, -100]) (count1589 q) 2 2 (meaning1586 q) (meaning1588 q) (meaning1592 q) hs
  change valuationOf q 1586 = false ∨ valuationOf q 1588 = false ∨ valuationOf q 1592 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1586 = false ∨ valuation q 1588 = false ∨ valuation q 1592 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1589 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_right (literal (valuationOf q) (1589)) (literal (valuationOf q) (1593)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 1 (meaning1589 q) (meaning1593 q) hs
  change valuationOf q 1589 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1589 = false ∨ valuation q 1593 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 1590 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_right (literal (valuationOf q) (1590)) (literal (valuationOf q) (1594)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 2 (meaning1590 q) (meaning1594 q) hs
  change valuationOf q 1590 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 1590 = false ∨ valuation q 1594 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 1591 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_right (literal (valuationOf q) (1591)) (literal (valuationOf q) (1595)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 3 (meaning1591 q) (meaning1595 q) hs
  change valuationOf q 1591 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 1591 = false ∨ valuation q 1595 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 1592 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_right (literal (valuationOf q) (1592)) (literal (valuationOf q) (1596)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 4 (meaning1592 q) (meaning1596 q) hs
  change valuationOf q 1592 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 1592 = false ∨ valuation q 1596 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1593 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_left (literal (valuationOf q) (1582)) (literal (valuationOf q) (1593)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 1 (meaning1582 q) (meaning1593 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1593 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1593 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1594)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 1 1 (meaning1582 q) (meaning1589 q) (meaning1594 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1589 = false ∨ valuation q 1594 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1595)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 1 2 (meaning1582 q) (meaning1590 q) (meaning1595 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1590 = false ∨ valuation q 1595 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1596)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 1 3 (meaning1582 q) (meaning1591 q) (meaning1596 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1591 = false ∨ valuation q 1596 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1582 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1597 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_two (literal (valuationOf q) (1582)) (literal (valuationOf q) (1592)) (literal (valuationOf q) (1597)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 1 4 (meaning1582 q) (meaning1592 q) (meaning1597 q) hs
  change valuationOf q 1582 = false ∨ valuationOf q 1592 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1582 = false ∨ valuation q 1592 = false ∨ valuation q 1597 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1594 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_left (literal (valuationOf q) (1583)) (literal (valuationOf q) (1594)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 2 (meaning1583 q) (meaning1594 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1594 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1594 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1589)) (literal (valuationOf q) (1595)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 2 1 (meaning1583 q) (meaning1589 q) (meaning1595 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1589 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1589 = false ∨ valuation q 1595 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1596 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1590)) (literal (valuationOf q) (1596)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 2 2 (meaning1583 q) (meaning1590 q) (meaning1596 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1590 = false ∨ valuationOf q 1596 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1590 = false ∨ valuation q 1596 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1583 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1597 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_two (literal (valuationOf q) (1583)) (literal (valuationOf q) (1591)) (literal (valuationOf q) (1597)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 2 3 (meaning1583 q) (meaning1591 q) (meaning1597 q) hs
  change valuationOf q 1583 = false ∨ valuationOf q 1591 = false ∨ valuationOf q 1597 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1583 = false ∨ valuation q 1591 = false ∨ valuation q 1597 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1584 = false ∨ valuationOf q 1595 = true := by
  have hs : count1593 q = (countLit q [-88, -91, -92]) + (countLit q [-94, -95, -96, -100]) := List.countP_append (p := literal q) (l₁ := [-88, -91, -92]) (l₂ := [-94, -95, -96, -100])
  have hm := merge_left (literal (valuationOf q) (1584)) (literal (valuationOf q) (1595)) (countLit q [-88, -91, -92]) (countLit q [-94, -95, -96, -100]) (count1593 q) 3 (meaning1584 q) (meaning1595 q) hs
  change valuationOf q 1584 = false ∨ valuationOf q 1595 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1584 = false ∨ valuation q 1595 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E120.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112120
