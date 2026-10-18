import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 742 = false ∨ valuationOf q 747 = false ∨ valuationOf q 751 = true := by
  have hs : count750 q = (countLit q [-27, -28, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_two (literal (valuationOf q) (742)) (literal (valuationOf q) (747)) (literal (valuationOf q) (751)) (countLit q [-27, -28, -31]) (countLit q [-33, -34, -36]) (count750 q) 1 1 (meaning742 q) (meaning747 q) (meaning751 q) hs
  change valuationOf q 742 = false ∨ valuationOf q 747 = false ∨ valuationOf q 751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 742 = false ∨ valuation q 747 = false ∨ valuation q 751 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 742 = false ∨ valuationOf q 748 = false ∨ valuationOf q 752 = true := by
  have hs : count750 q = (countLit q [-27, -28, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_two (literal (valuationOf q) (742)) (literal (valuationOf q) (748)) (literal (valuationOf q) (752)) (countLit q [-27, -28, -31]) (countLit q [-33, -34, -36]) (count750 q) 1 2 (meaning742 q) (meaning748 q) (meaning752 q) hs
  change valuationOf q 742 = false ∨ valuationOf q 748 = false ∨ valuationOf q 752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 742 = false ∨ valuation q 748 = false ∨ valuation q 752 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 743 = false ∨ valuationOf q 751 = true := by
  have hs : count750 q = (countLit q [-27, -28, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_left (literal (valuationOf q) (743)) (literal (valuationOf q) (751)) (countLit q [-27, -28, -31]) (countLit q [-33, -34, -36]) (count750 q) 2 (meaning743 q) (meaning751 q) hs
  change valuationOf q 743 = false ∨ valuationOf q 751 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 743 = false ∨ valuation q 751 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 743 = false ∨ valuationOf q 747 = false ∨ valuationOf q 752 = true := by
  have hs : count750 q = (countLit q [-27, -28, -31]) + (countLit q [-33, -34, -36]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31]) (l₂ := [-33, -34, -36])
  have hm := merge_two (literal (valuationOf q) (743)) (literal (valuationOf q) (747)) (literal (valuationOf q) (752)) (countLit q [-27, -28, -31]) (countLit q [-33, -34, -36]) (count750 q) 2 1 (meaning743 q) (meaning747 q) (meaning752 q) hs
  change valuationOf q 743 = false ∨ valuationOf q 747 = false ∨ valuationOf q 752 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 743 = false ∨ valuation q 747 = false ∨ valuation q 752 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 756 = true := by
  have hs : count756 q = (countLit q [-41]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43])
  have hm := merge_right (literal (valuationOf q) (-43)) (literal (valuationOf q) (756)) (countLit q [-41]) (countLit q [-43]) (count756 q) 1 (meaningNeg43 q) (meaning756 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 756 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 756 = true := by
  have hs : count756 q = (countLit q [-41]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43])
  have hm := merge_left (literal (valuationOf q) (-41)) (literal (valuationOf q) (756)) (countLit q [-41]) (countLit q [-43]) (count756 q) 1 (meaningNeg41 q) (meaning756 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 756 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 756 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 43 = true ∨ valuationOf q 757 = true := by
  have hs : count756 q = (countLit q [-41]) + (countLit q [-43]) := List.countP_append (p := literal q) (l₁ := [-41]) (l₂ := [-43])
  have hm := merge_two (literal (valuationOf q) (-41)) (literal (valuationOf q) (-43)) (literal (valuationOf q) (757)) (countLit q [-41]) (countLit q [-43]) (count756 q) 1 1 (meaningNeg41 q) (meaningNeg43 q) (meaning757 q) hs
  change (! (valuationOf q 41)) = false ∨ (! (valuationOf q 43)) = false ∨ valuationOf q 757 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 43 = true ∨ valuation q 757 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 756 = false ∨ valuationOf q 758 = true := by
  have hs : count758 q = (countLit q [-38]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -43])
  have hm := merge_right (literal (valuationOf q) (756)) (literal (valuationOf q) (758)) (countLit q [-38]) (countLit q [-41, -43]) (count758 q) 1 (meaning756 q) (meaning758 q) hs
  change valuationOf q 756 = false ∨ valuationOf q 758 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 756 = false ∨ valuation q 758 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 759 = true := by
  have hs : count758 q = (countLit q [-38]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -43])
  have hm := merge_right (literal (valuationOf q) (757)) (literal (valuationOf q) (759)) (countLit q [-38]) (countLit q [-41, -43]) (count758 q) 2 (meaning757 q) (meaning759 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 759 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 756 = false ∨ valuationOf q 759 = true := by
  have hs : count758 q = (countLit q [-38]) + (countLit q [-41, -43]) := List.countP_append (p := literal q) (l₁ := [-38]) (l₂ := [-41, -43])
  have hm := merge_two (literal (valuationOf q) (-38)) (literal (valuationOf q) (756)) (literal (valuationOf q) (759)) (countLit q [-38]) (countLit q [-41, -43]) (count758 q) 1 1 (meaningNeg38 q) (meaning756 q) (meaning759 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 756 = false ∨ valuationOf q 759 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 756 = false ∨ valuation q 759 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 761 = true := by
  have hs : count761 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (761)) (countLit q [-45]) (countLit q [-48]) (count761 q) 1 (meaningNeg48 q) (meaning761 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 761 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 761 = true := by
  have hs : count761 q = (countLit q [-45]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-45]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-45)) (literal (valuationOf q) (761)) (countLit q [-45]) (countLit q [-48]) (count761 q) 1 (meaningNeg45 q) (meaning761 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 761 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 761 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 763 = true := by
  have hs : count763 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (763)) (countLit q [-50]) (countLit q [-51]) (count763 q) 1 (meaningNeg51 q) (meaning763 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 763 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 763 = true := by
  have hs : count763 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (763)) (countLit q [-50]) (countLit q [-51]) (count763 q) 1 (meaningNeg50 q) (meaning763 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 763 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 763 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 51 = true ∨ valuationOf q 764 = true := by
  have hs : count763 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (764)) (countLit q [-50]) (countLit q [-51]) (count763 q) 1 1 (meaningNeg50 q) (meaningNeg51 q) (meaning764 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 764 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 764 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 763 = false ∨ valuationOf q 765 = true := by
  have hs : count765 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (763)) (literal (valuationOf q) (765)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count765 q) 1 (meaning763 q) (meaning765 q) hs
  change valuationOf q 763 = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 763 = false ∨ valuation q 765 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 764 = false ∨ valuationOf q 766 = true := by
  have hs : count765 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_right (literal (valuationOf q) (764)) (literal (valuationOf q) (766)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count765 q) 2 (meaning764 q) (meaning766 q) hs
  change valuationOf q 764 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 764 = false ∨ valuation q 766 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 761 = false ∨ valuationOf q 765 = true := by
  have hs : count765 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_left (literal (valuationOf q) (761)) (literal (valuationOf q) (765)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count765 q) 1 (meaning761 q) (meaning765 q) hs
  change valuationOf q 761 = false ∨ valuationOf q 765 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 761 = false ∨ valuation q 765 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 761 = false ∨ valuationOf q 763 = false ∨ valuationOf q 766 = true := by
  have hs : count765 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (761)) (literal (valuationOf q) (763)) (literal (valuationOf q) (766)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count765 q) 1 1 (meaning761 q) (meaning763 q) (meaning766 q) hs
  change valuationOf q 761 = false ∨ valuationOf q 763 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 761 = false ∨ valuation q 763 = false ∨ valuation q 766 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 761 = false ∨ valuationOf q 764 = false ∨ valuationOf q 767 = true := by
  have hs : count765 q = (countLit q [-45, -48]) + (countLit q [-50, -51]) := List.countP_append (p := literal q) (l₁ := [-45, -48]) (l₂ := [-50, -51])
  have hm := merge_two (literal (valuationOf q) (761)) (literal (valuationOf q) (764)) (literal (valuationOf q) (767)) (countLit q [-45, -48]) (countLit q [-50, -51]) (count765 q) 1 2 (meaning761 q) (meaning764 q) (meaning767 q) hs
  change valuationOf q 761 = false ∨ valuationOf q 764 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 761 = false ∨ valuation q 764 = false ∨ valuation q 767 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 765 = false ∨ valuationOf q 769 = true := by
  have hs : count769 q = (countLit q [-38, -41, -43]) + (countLit q [-45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-45, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (765)) (literal (valuationOf q) (769)) (countLit q [-38, -41, -43]) (countLit q [-45, -48, -50, -51]) (count769 q) 1 (meaning765 q) (meaning769 q) hs
  change valuationOf q 765 = false ∨ valuationOf q 769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 765 = false ∨ valuation q 769 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 766 = false ∨ valuationOf q 770 = true := by
  have hs : count769 q = (countLit q [-38, -41, -43]) + (countLit q [-45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-45, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (766)) (literal (valuationOf q) (770)) (countLit q [-38, -41, -43]) (countLit q [-45, -48, -50, -51]) (count769 q) 2 (meaning766 q) (meaning770 q) hs
  change valuationOf q 766 = false ∨ valuationOf q 770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 766 = false ∨ valuation q 770 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 767 = false ∨ valuationOf q 771 = true := by
  have hs : count769 q = (countLit q [-38, -41, -43]) + (countLit q [-45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-45, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (767)) (literal (valuationOf q) (771)) (countLit q [-38, -41, -43]) (countLit q [-45, -48, -50, -51]) (count769 q) 3 (meaning767 q) (meaning771 q) hs
  change valuationOf q 767 = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 767 = false ∨ valuation q 771 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 769 = true := by
  have hs : count769 q = (countLit q [-38, -41, -43]) + (countLit q [-45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-45, -48, -50, -51])
  have hm := merge_left (literal (valuationOf q) (758)) (literal (valuationOf q) (769)) (countLit q [-38, -41, -43]) (countLit q [-45, -48, -50, -51]) (count769 q) 1 (meaning758 q) (meaning769 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 769 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 769 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 765 = false ∨ valuationOf q 770 = true := by
  have hs : count769 q = (countLit q [-38, -41, -43]) + (countLit q [-45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (765)) (literal (valuationOf q) (770)) (countLit q [-38, -41, -43]) (countLit q [-45, -48, -50, -51]) (count769 q) 1 1 (meaning758 q) (meaning765 q) (meaning770 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 765 = false ∨ valuationOf q 770 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 765 = false ∨ valuation q 770 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 766 = false ∨ valuationOf q 771 = true := by
  have hs : count769 q = (countLit q [-38, -41, -43]) + (countLit q [-45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (766)) (literal (valuationOf q) (771)) (countLit q [-38, -41, -43]) (countLit q [-45, -48, -50, -51]) (count769 q) 1 2 (meaning758 q) (meaning766 q) (meaning771 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 766 = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 766 = false ∨ valuation q 771 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 765 = false ∨ valuationOf q 771 = true := by
  have hs : count769 q = (countLit q [-38, -41, -43]) + (countLit q [-45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (765)) (literal (valuationOf q) (771)) (countLit q [-38, -41, -43]) (countLit q [-45, -48, -50, -51]) (count769 q) 2 1 (meaning759 q) (meaning765 q) (meaning771 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 765 = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 765 = false ∨ valuation q 771 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 759 = false ∨ valuationOf q 766 = false ∨ valuationOf q 772 = true := by
  have hs : count769 q = (countLit q [-38, -41, -43]) + (countLit q [-45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-38, -41, -43]) (l₂ := [-45, -48, -50, -51])
  have hm := merge_two (literal (valuationOf q) (759)) (literal (valuationOf q) (766)) (literal (valuationOf q) (772)) (countLit q [-38, -41, -43]) (countLit q [-45, -48, -50, -51]) (count769 q) 2 2 (meaning759 q) (meaning766 q) (meaning772 q) hs
  change valuationOf q 759 = false ∨ valuationOf q 766 = false ∨ valuationOf q 772 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 759 = false ∨ valuation q 766 = false ∨ valuation q 772 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 769 = false ∨ valuationOf q 776 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (769)) (literal (valuationOf q) (776)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 1 (meaning769 q) (meaning776 q) hs
  change valuationOf q 769 = false ∨ valuationOf q 776 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 769 = false ∨ valuation q 776 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 770 = false ∨ valuationOf q 777 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (770)) (literal (valuationOf q) (777)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 2 (meaning770 q) (meaning777 q) hs
  change valuationOf q 770 = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 770 = false ∨ valuation q 777 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 771 = false ∨ valuationOf q 778 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (771)) (literal (valuationOf q) (778)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 3 (meaning771 q) (meaning778 q) hs
  change valuationOf q 771 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 771 = false ∨ valuation q 778 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 772 = false ∨ valuationOf q 779 = true := by
  have hs : count776 q = (countLit q [-27, -28, -31, -33, -34, -36]) + (countLit q [-38, -41, -43, -45, -48, -50, -51]) := List.countP_append (p := literal q) (l₁ := [-27, -28, -31, -33, -34, -36]) (l₂ := [-38, -41, -43, -45, -48, -50, -51])
  have hm := merge_right (literal (valuationOf q) (772)) (literal (valuationOf q) (779)) (countLit q [-27, -28, -31, -33, -34, -36]) (countLit q [-38, -41, -43, -45, -48, -50, -51]) (count776 q) 4 (meaning772 q) (meaning779 q) hs
  change valuationOf q 772 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 772 = false ∨ valuation q 779 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E174.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112174
