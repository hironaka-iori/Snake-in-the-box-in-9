import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 707 = false ∨ valuationOf q 723 = false ∨ valuationOf q 730 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (707)) (literal (valuationOf q) (723)) (literal (valuationOf q) (730)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 1 1 (meaning707 q) (meaning723 q) (meaning730 q) hs
  change valuationOf q 707 = false ∨ valuationOf q 723 = false ∨ valuationOf q 730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 707 = false ∨ valuation q 723 = false ∨ valuation q 730 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 707 = false ∨ valuationOf q 724 = false ∨ valuationOf q 731 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (707)) (literal (valuationOf q) (724)) (literal (valuationOf q) (731)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 1 2 (meaning707 q) (meaning724 q) (meaning731 q) hs
  change valuationOf q 707 = false ∨ valuationOf q 724 = false ∨ valuationOf q 731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 707 = false ∨ valuation q 724 = false ∨ valuation q 731 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 708 = false ∨ valuationOf q 730 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (708)) (literal (valuationOf q) (730)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 2 (meaning708 q) (meaning730 q) hs
  change valuationOf q 708 = false ∨ valuationOf q 730 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 708 = false ∨ valuation q 730 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 708 = false ∨ valuationOf q 723 = false ∨ valuationOf q 731 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (708)) (literal (valuationOf q) (723)) (literal (valuationOf q) (731)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 2 1 (meaning708 q) (meaning723 q) (meaning731 q) hs
  change valuationOf q 708 = false ∨ valuationOf q 723 = false ∨ valuationOf q 731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 708 = false ∨ valuation q 723 = false ∨ valuation q 731 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 708 = false ∨ valuationOf q 724 = false ∨ valuationOf q 732 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (708)) (literal (valuationOf q) (724)) (literal (valuationOf q) (732)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 2 2 (meaning708 q) (meaning724 q) (meaning732 q) hs
  change valuationOf q 708 = false ∨ valuationOf q 724 = false ∨ valuationOf q 732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 708 = false ∨ valuation q 724 = false ∨ valuation q 732 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 708 = false ∨ valuationOf q 725 = false ∨ valuationOf q 733 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (708)) (literal (valuationOf q) (725)) (literal (valuationOf q) (733)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 2 3 (meaning708 q) (meaning725 q) (meaning733 q) hs
  change valuationOf q 708 = false ∨ valuationOf q 725 = false ∨ valuationOf q 733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 708 = false ∨ valuation q 725 = false ∨ valuation q 733 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 709 = false ∨ valuationOf q 731 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (709)) (literal (valuationOf q) (731)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 3 (meaning709 q) (meaning731 q) hs
  change valuationOf q 709 = false ∨ valuationOf q 731 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 709 = false ∨ valuation q 731 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 709 = false ∨ valuationOf q 723 = false ∨ valuationOf q 732 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (709)) (literal (valuationOf q) (723)) (literal (valuationOf q) (732)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 3 1 (meaning709 q) (meaning723 q) (meaning732 q) hs
  change valuationOf q 709 = false ∨ valuationOf q 723 = false ∨ valuationOf q 732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 709 = false ∨ valuation q 723 = false ∨ valuation q 732 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 709 = false ∨ valuationOf q 724 = false ∨ valuationOf q 733 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (709)) (literal (valuationOf q) (724)) (literal (valuationOf q) (733)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 3 2 (meaning709 q) (meaning724 q) (meaning733 q) hs
  change valuationOf q 709 = false ∨ valuationOf q 724 = false ∨ valuationOf q 733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 709 = false ∨ valuation q 724 = false ∨ valuation q 733 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 709 = false ∨ valuationOf q 725 = false ∨ valuationOf q 734 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (709)) (literal (valuationOf q) (725)) (literal (valuationOf q) (734)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 3 3 (meaning709 q) (meaning725 q) (meaning734 q) hs
  change valuationOf q 709 = false ∨ valuationOf q 725 = false ∨ valuationOf q 734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 709 = false ∨ valuation q 725 = false ∨ valuation q 734 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 710 = false ∨ valuationOf q 732 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (710)) (literal (valuationOf q) (732)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 4 (meaning710 q) (meaning732 q) hs
  change valuationOf q 710 = false ∨ valuationOf q 732 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 710 = false ∨ valuation q 732 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 710 = false ∨ valuationOf q 723 = false ∨ valuationOf q 733 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (710)) (literal (valuationOf q) (723)) (literal (valuationOf q) (733)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 4 1 (meaning710 q) (meaning723 q) (meaning733 q) hs
  change valuationOf q 710 = false ∨ valuationOf q 723 = false ∨ valuationOf q 733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 710 = false ∨ valuation q 723 = false ∨ valuation q 733 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 710 = false ∨ valuationOf q 724 = false ∨ valuationOf q 734 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (710)) (literal (valuationOf q) (724)) (literal (valuationOf q) (734)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 4 2 (meaning710 q) (meaning724 q) (meaning734 q) hs
  change valuationOf q 710 = false ∨ valuationOf q 724 = false ∨ valuationOf q 734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 710 = false ∨ valuation q 724 = false ∨ valuation q 734 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 711 = false ∨ valuationOf q 733 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_left (literal (valuationOf q) (711)) (literal (valuationOf q) (733)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 5 (meaning711 q) (meaning733 q) hs
  change valuationOf q 711 = false ∨ valuationOf q 733 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 711 = false ∨ valuation q 733 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 711 = false ∨ valuationOf q 723 = false ∨ valuationOf q 734 = true := by
  have hs : count729 q = (countLit q [-3, -4, -6, -10, -12, -14]) + (countLit q [-16, -17, -18, -21, -22, -25]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6, -10, -12, -14]) (l₂ := [-16, -17, -18, -21, -22, -25])
  have hm := merge_two (literal (valuationOf q) (711)) (literal (valuationOf q) (723)) (literal (valuationOf q) (734)) (countLit q [-3, -4, -6, -10, -12, -14]) (countLit q [-16, -17, -18, -21, -22, -25]) (count729 q) 5 1 (meaning711 q) (meaning723 q) (meaning734 q) hs
  change valuationOf q 711 = false ∨ valuationOf q 723 = false ∨ valuationOf q 734 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 711 = false ∨ valuation q 723 = false ∨ valuation q 734 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 740 = true := by
  have hs : count740 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_right (literal (valuationOf q) (-31)) (literal (valuationOf q) (740)) (countLit q [-28]) (countLit q [-31]) (count740 q) 1 (meaningNeg31 q) (meaning740 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 740 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 740 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 740 = true := by
  have hs : count740 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (740)) (countLit q [-28]) (countLit q [-31]) (count740 q) 1 (meaningNeg28 q) (meaning740 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 740 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 740 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 31 = true ∨ valuationOf q 741 = true := by
  have hs : count740 q = (countLit q [-28]) + (countLit q [-31]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-31])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-31)) (literal (valuationOf q) (741)) (countLit q [-28]) (countLit q [-31]) (count740 q) 1 1 (meaningNeg28 q) (meaningNeg31 q) (meaning741 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 31)) = false ∨ valuationOf q 741 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 31 = true ∨ valuation q 741 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 740 = false ∨ valuationOf q 742 = true := by
  have hs : count742 q = (countLit q [-27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (740)) (literal (valuationOf q) (742)) (countLit q [-27]) (countLit q [-28, -31]) (count742 q) 1 (meaning740 q) (meaning742 q) hs
  change valuationOf q 740 = false ∨ valuationOf q 742 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 740 = false ∨ valuation q 742 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 741 = false ∨ valuationOf q 743 = true := by
  have hs : count742 q = (countLit q [-27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28, -31])
  have hm := merge_right (literal (valuationOf q) (741)) (literal (valuationOf q) (743)) (countLit q [-27]) (countLit q [-28, -31]) (count742 q) 2 (meaning741 q) (meaning743 q) hs
  change valuationOf q 741 = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 741 = false ∨ valuation q 743 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 742 = true := by
  have hs : count742 q = (countLit q [-27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28, -31])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (742)) (countLit q [-27]) (countLit q [-28, -31]) (count742 q) 1 (meaningNeg27 q) (meaning742 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 742 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 742 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 740 = false ∨ valuationOf q 743 = true := by
  have hs : count742 q = (countLit q [-27]) + (countLit q [-28, -31]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-28, -31])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (740)) (literal (valuationOf q) (743)) (countLit q [-27]) (countLit q [-28, -31]) (count742 q) 1 1 (meaningNeg27 q) (meaning740 q) (meaning743 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 740 = false ∨ valuationOf q 743 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 740 = false ∨ valuation q 743 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 745 = true := by
  have hs : count745 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (745)) (countLit q [-34]) (countLit q [-36]) (count745 q) 1 (meaningNeg36 q) (meaning745 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 745 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 745 = true := by
  have hs : count745 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_left (literal (valuationOf q) (-34)) (literal (valuationOf q) (745)) (countLit q [-34]) (countLit q [-36]) (count745 q) 1 (meaningNeg34 q) (meaning745 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 745 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 745 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 36 = true ∨ valuationOf q 746 = true := by
  have hs : count745 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_two (literal (valuationOf q) (-34)) (literal (valuationOf q) (-36)) (literal (valuationOf q) (746)) (countLit q [-34]) (countLit q [-36]) (count745 q) 1 1 (meaningNeg34 q) (meaningNeg36 q) (meaning746 q) hs
  change (! (valuationOf q 34)) = false ∨ (! (valuationOf q 36)) = false ∨ valuationOf q 746 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 36 = true ∨ valuation q 746 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 745 = false ∨ valuationOf q 747 = true := by
  have hs : count747 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (745)) (literal (valuationOf q) (747)) (countLit q [-33]) (countLit q [-34, -36]) (count747 q) 1 (meaning745 q) (meaning747 q) hs
  change valuationOf q 745 = false ∨ valuationOf q 747 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 745 = false ∨ valuation q 747 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 746 = false ∨ valuationOf q 748 = true := by
  have hs : count747 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_right (literal (valuationOf q) (746)) (literal (valuationOf q) (748)) (countLit q [-33]) (countLit q [-34, -36]) (count747 q) 2 (meaning746 q) (meaning748 q) hs
  change valuationOf q 746 = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 746 = false ∨ valuation q 748 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 747 = true := by
  have hs : count747 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_left (literal (valuationOf q) (-33)) (literal (valuationOf q) (747)) (countLit q [-33]) (countLit q [-34, -36]) (count747 q) 1 (meaningNeg33 q) (meaning747 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 747 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 747 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 745 = false ∨ valuationOf q 748 = true := by
  have hs : count747 q = (countLit q [-33]) + (countLit q [-34, -36]) := List.countP_append (p := literal q) (l₁ := [-33]) (l₂ := [-34, -36])
  have hm := merge_two (literal (valuationOf q) (-33)) (literal (valuationOf q) (745)) (literal (valuationOf q) (748)) (countLit q [-33]) (countLit q [-34, -36]) (count747 q) 1 1 (meaningNeg33 q) (meaning745 q) (meaning748 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 745 = false ∨ valuationOf q 748 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 745 = false ∨ valuation q 748 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 747 = false ∨ valuationOf q 750 = true := by
  have hs : count750 q = (countLit q [-27, -28, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_right (literal (valuationOf q) (747)) (literal (valuationOf q) (750)) (countLit q [-27, -28, -31]) (countLit q [-33, -34, -36]) (count750 q) 1 (meaning747 q) (meaning750 q) hs
  change valuationOf q 747 = false ∨ valuationOf q 750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 747 = false ∨ valuation q 750 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 748 = false ∨ valuationOf q 751 = true := by
  have hs : count750 q = (countLit q [-27, -28, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_right (literal (valuationOf q) (748)) (literal (valuationOf q) (751)) (countLit q [-27, -28, -31]) (countLit q [-33, -34, -36]) (count750 q) 2 (meaning748 q) (meaning751 q) hs
  change valuationOf q 748 = false ∨ valuationOf q 751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 748 = false ∨ valuation q 751 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 742 = false ∨ valuationOf q 750 = true := by
  have hs : count750 q = (countLit q [-27, -28, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_left (literal (valuationOf q) (742)) (literal (valuationOf q) (750)) (countLit q [-27, -28, -31]) (countLit q [-33, -34, -36]) (count750 q) 1 (meaning742 q) (meaning750 q) hs
  change valuationOf q 742 = false ∨ valuationOf q 750 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 742 = false ∨ valuation q 750 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E174.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112174
