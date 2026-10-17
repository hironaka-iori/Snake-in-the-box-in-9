import E112185Semantics
import B112E185Inputs
namespace Snake9.Regrowth.E112185
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 764 = false ∨ valuationOf q 766 = true := by
  have hs : count765 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_right (literal (valuationOf q) (764)) (literal (valuationOf q) (766)) (countLit q [-15]) (countLit q [-17, -18]) (count765 q) 2 (meaning764 q) (meaning766 q) hs
  change valuationOf q 764 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 764 = false ∨ valuation q 766 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 765 = true := by
  have hs : count765 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (765)) (countLit q [-15]) (countLit q [-17, -18]) (count765 q) 1 (meaningNeg15 q) (meaning765 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 765 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 763 = false ∨ valuationOf q 766 = true := by
  have hs : count765 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (763)) (literal (valuationOf q) (766)) (countLit q [-15]) (countLit q [-17, -18]) (count765 q) 1 1 (meaningNeg15 q) (meaning763 q) (meaning766 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 763 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 763 = false ∨ valuation q 766 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 764 = false ∨ valuationOf q 767 = true := by
  have hs : count765 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (764)) (literal (valuationOf q) (767)) (countLit q [-15]) (countLit q [-17, -18]) (count765 q) 1 2 (meaningNeg15 q) (meaning764 q) (meaning767 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 764 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 764 = false ∨ valuation q 767 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 768 = true := by
  have hs : count768 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (768)) (countLit q [-20]) (countLit q [-21]) (count768 q) 1 (meaningNeg21 q) (meaning768 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 768 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 768 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 768 = true := by
  have hs : count768 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (768)) (countLit q [-20]) (countLit q [-21]) (count768 q) 1 (meaningNeg20 q) (meaning768 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 768 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 768 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 21 = true ∨ valuationOf q 769 = true := by
  have hs : count768 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-21)) (literal (valuationOf q) (769)) (countLit q [-20]) (countLit q [-21]) (count768 q) 1 1 (meaningNeg20 q) (meaningNeg21 q) (meaning769 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 21)) = false ∨ valuationOf q 769 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 21 = true ∨ valuation q 769 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 770 = true := by
  have hs : count770 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (770)) (countLit q [-24]) (countLit q [-25]) (count770 q) 1 (meaningNeg25 q) (meaning770 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 770 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 770 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 771 = true := by
  have hs : count770 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (771)) (countLit q [-24]) (countLit q [-25]) (count770 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning771 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 771 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 770 = false ∨ valuationOf q 772 = true := by
  have hs : count772 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (770)) (literal (valuationOf q) (772)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count772 q) 1 (meaning770 q) (meaning772 q) hs
  change valuationOf q 770 = false ∨ valuationOf q 772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 770 = false ∨ valuation q 772 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 768 = false ∨ valuationOf q 770 = false ∨ valuationOf q 773 = true := by
  have hs : count772 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (768)) (literal (valuationOf q) (770)) (literal (valuationOf q) (773)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count772 q) 1 1 (meaning768 q) (meaning770 q) (meaning773 q) hs
  change valuationOf q 768 = false ∨ valuationOf q 770 = false ∨ valuationOf q 773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 768 = false ∨ valuation q 770 = false ∨ valuation q 773 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 768 = false ∨ valuationOf q 771 = false ∨ valuationOf q 774 = true := by
  have hs : count772 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (768)) (literal (valuationOf q) (771)) (literal (valuationOf q) (774)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count772 q) 1 2 (meaning768 q) (meaning771 q) (meaning774 q) hs
  change valuationOf q 768 = false ∨ valuationOf q 771 = false ∨ valuationOf q 774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 768 = false ∨ valuation q 771 = false ∨ valuation q 774 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 769 = false ∨ valuationOf q 770 = false ∨ valuationOf q 774 = true := by
  have hs : count772 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (769)) (literal (valuationOf q) (770)) (literal (valuationOf q) (774)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count772 q) 2 1 (meaning769 q) (meaning770 q) (meaning774 q) hs
  change valuationOf q 769 = false ∨ valuationOf q 770 = false ∨ valuationOf q 774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 769 = false ∨ valuation q 770 = false ∨ valuation q 774 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 769 = false ∨ valuationOf q 771 = false ∨ valuationOf q 775 = true := by
  have hs : count772 q = (countLit q [-20, -21]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-20, -21]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (769)) (literal (valuationOf q) (771)) (literal (valuationOf q) (775)) (countLit q [-20, -21]) (countLit q [-24, -25]) (count772 q) 2 2 (meaning769 q) (meaning771 q) (meaning775 q) hs
  change valuationOf q 769 = false ∨ valuationOf q 771 = false ∨ valuationOf q 775 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 769 = false ∨ valuation q 771 = false ∨ valuation q 775 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 772 = false ∨ valuationOf q 776 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_right (literal (valuationOf q) (772)) (literal (valuationOf q) (776)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 1 (meaning772 q) (meaning776 q) hs
  change valuationOf q 772 = false ∨ valuationOf q 776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 772 = false ∨ valuation q 776 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 773 = false ∨ valuationOf q 777 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_right (literal (valuationOf q) (773)) (literal (valuationOf q) (777)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 2 (meaning773 q) (meaning777 q) hs
  change valuationOf q 773 = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 773 = false ∨ valuation q 777 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 774 = false ∨ valuationOf q 778 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_right (literal (valuationOf q) (774)) (literal (valuationOf q) (778)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 3 (meaning774 q) (meaning778 q) hs
  change valuationOf q 774 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 774 = false ∨ valuation q 778 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 772 = false ∨ valuationOf q 777 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (765)) (literal (valuationOf q) (772)) (literal (valuationOf q) (777)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 1 1 (meaning765 q) (meaning772 q) (meaning777 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 772 = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 772 = false ∨ valuation q 777 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 773 = false ∨ valuationOf q 778 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (765)) (literal (valuationOf q) (773)) (literal (valuationOf q) (778)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 1 2 (meaning765 q) (meaning773 q) (meaning778 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 773 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 773 = false ∨ valuation q 778 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 774 = false ∨ valuationOf q 779 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (765)) (literal (valuationOf q) (774)) (literal (valuationOf q) (779)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 1 3 (meaning765 q) (meaning774 q) (meaning779 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 774 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 774 = false ∨ valuation q 779 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 775 = false ∨ valuationOf q 780 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (765)) (literal (valuationOf q) (775)) (literal (valuationOf q) (780)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 1 4 (meaning765 q) (meaning775 q) (meaning780 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 775 = false ∨ valuationOf q 780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 775 = false ∨ valuation q 780 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 766 = false ∨ valuationOf q 773 = false ∨ valuationOf q 779 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (766)) (literal (valuationOf q) (773)) (literal (valuationOf q) (779)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 2 2 (meaning766 q) (meaning773 q) (meaning779 q) hs
  change valuationOf q 766 = false ∨ valuationOf q 773 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 766 = false ∨ valuation q 773 = false ∨ valuation q 779 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 766 = false ∨ valuationOf q 774 = false ∨ valuationOf q 780 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (766)) (literal (valuationOf q) (774)) (literal (valuationOf q) (780)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 2 3 (meaning766 q) (meaning774 q) (meaning780 q) hs
  change valuationOf q 766 = false ∨ valuationOf q 774 = false ∨ valuationOf q 780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 766 = false ∨ valuation q 774 = false ∨ valuation q 780 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 767 = false ∨ valuationOf q 772 = false ∨ valuationOf q 779 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (767)) (literal (valuationOf q) (772)) (literal (valuationOf q) (779)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 3 1 (meaning767 q) (meaning772 q) (meaning779 q) hs
  change valuationOf q 767 = false ∨ valuationOf q 772 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 767 = false ∨ valuation q 772 = false ∨ valuation q 779 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 767 = false ∨ valuationOf q 773 = false ∨ valuationOf q 780 = true := by
  have hs : count776 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (767)) (literal (valuationOf q) (773)) (literal (valuationOf q) (780)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count776 q) 3 2 (meaning767 q) (meaning773 q) (meaning780 q) hs
  change valuationOf q 767 = false ∨ valuationOf q 773 = false ∨ valuationOf q 780 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 767 = false ∨ valuation q 773 = false ∨ valuation q 780 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 756 = false ∨ valuationOf q 778 = false ∨ valuationOf q 786 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (756)) (literal (valuationOf q) (778)) (literal (valuationOf q) (786)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 1 3 (meaning756 q) (meaning778 q) (meaning786 q) hs
  change valuationOf q 756 = false ∨ valuationOf q 778 = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 756 = false ∨ valuation q 778 = false ∨ valuation q 786 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 778 = false ∨ valuationOf q 787 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (757)) (literal (valuationOf q) (778)) (literal (valuationOf q) (787)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 2 3 (meaning757 q) (meaning778 q) (meaning787 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 778 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 778 = false ∨ valuation q 787 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 779 = false ∨ valuationOf q 788 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (757)) (literal (valuationOf q) (779)) (literal (valuationOf q) (788)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 2 4 (meaning757 q) (meaning779 q) (meaning788 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 779 = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 779 = false ∨ valuation q 788 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 780 = false ∨ valuationOf q 789 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (757)) (literal (valuationOf q) (780)) (literal (valuationOf q) (789)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 2 5 (meaning757 q) (meaning780 q) (meaning789 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 780 = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 780 = false ∨ valuation q 789 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 776 = false ∨ valuationOf q 786 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (776)) (literal (valuationOf q) (786)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 3 1 (meaning758 q) (meaning776 q) (meaning786 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 776 = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 776 = false ∨ valuation q 786 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 777 = false ∨ valuationOf q 787 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (777)) (literal (valuationOf q) (787)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 3 2 (meaning758 q) (meaning777 q) (meaning787 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 777 = false ∨ valuationOf q 787 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 777 = false ∨ valuation q 787 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 778 = false ∨ valuationOf q 788 = true := by
  have hs : count783 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (778)) (literal (valuationOf q) (788)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count783 q) 3 3 (meaning758 q) (meaning778 q) (meaning788 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 778 = false ∨ valuationOf q 788 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 778 = false ∨ valuation q 788 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E185.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112185
