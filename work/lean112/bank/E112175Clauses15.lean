import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec15 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause481 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 764 = true := by
  have hs : count764 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (764)) (countLit q [-28]) (countLit q [-29]) (count764 q) 1 (meaningNeg28 q) (meaning764 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 764 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause481 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 764 = true := counterClause481 (baseVal q)

theorem counterClause482 (q : Nat → Bool) : valuationOf q 764 = false ∨ valuationOf q 766 = true := by
  have hs : count766 q = (countLit q [-26]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28, -29])
  have hm := merge_right (literal (valuationOf q) (764)) (literal (valuationOf q) (766)) (countLit q [-26]) (countLit q [-28, -29]) (count766 q) 1 (meaning764 q) (meaning766 q) hs
  change valuationOf q 764 = false ∨ valuationOf q 766 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause482 (q : Snake 81) (h : Conditions q) : valuation q 764 = false ∨ valuation q 766 = true := counterClause482 (baseVal q)

theorem counterClause483 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 764 = false ∨ valuationOf q 767 = true := by
  have hs : count766 q = (countLit q [-26]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-28, -29])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (764)) (literal (valuationOf q) (767)) (countLit q [-26]) (countLit q [-28, -29]) (count766 q) 1 1 (meaningNeg26 q) (meaning764 q) (meaning767 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 764 = false ∨ valuationOf q 767 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause483 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 764 = false ∨ valuation q 767 = true := counterClause483 (baseVal q)

theorem counterClause484 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 769 = true := by
  have hs : count769 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_right (literal (valuationOf q) (-32)) (literal (valuationOf q) (769)) (countLit q [-31]) (countLit q [-32]) (count769 q) 1 (meaningNeg32 q) (meaning769 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 769 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause484 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 769 = true := counterClause484 (baseVal q)

theorem counterClause485 (q : Nat → Bool) : valuationOf q 31 = true ∨ valuationOf q 769 = true := by
  have hs : count769 q = (countLit q [-31]) + (countLit q [-32]) := List.countP_append (p := literal q) (l₁ := [-31]) (l₂ := [-32])
  have hm := merge_left (literal (valuationOf q) (-31)) (literal (valuationOf q) (769)) (countLit q [-31]) (countLit q [-32]) (count769 q) 1 (meaningNeg31 q) (meaning769 q) hs
  change (! (valuationOf q 31)) = false ∨ valuationOf q 769 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause485 (q : Snake 81) (h : Conditions q) : valuation q 31 = true ∨ valuation q 769 = true := counterClause485 (baseVal q)

theorem counterClause486 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 771 = true := by
  have hs : count771 q = (countLit q [-34]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (771)) (countLit q [-34]) (countLit q [-37]) (count771 q) 1 (meaningNeg37 q) (meaning771 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 771 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause486 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 771 = true := counterClause486 (baseVal q)

theorem counterClause487 (q : Nat → Bool) : valuationOf q 771 = false ∨ valuationOf q 773 = true := by
  have hs : count773 q = (countLit q [-31, -32]) + (countLit q [-34, -37]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -37])
  have hm := merge_right (literal (valuationOf q) (771)) (literal (valuationOf q) (773)) (countLit q [-31, -32]) (countLit q [-34, -37]) (count773 q) 1 (meaning771 q) (meaning773 q) hs
  change valuationOf q 771 = false ∨ valuationOf q 773 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause487 (q : Snake 81) (h : Conditions q) : valuation q 771 = false ∨ valuation q 773 = true := counterClause487 (baseVal q)

theorem counterClause488 (q : Nat → Bool) : valuationOf q 769 = false ∨ valuationOf q 771 = false ∨ valuationOf q 774 = true := by
  have hs : count773 q = (countLit q [-31, -32]) + (countLit q [-34, -37]) := List.countP_append (p := literal q) (l₁ := [-31, -32]) (l₂ := [-34, -37])
  have hm := merge_two (literal (valuationOf q) (769)) (literal (valuationOf q) (771)) (literal (valuationOf q) (774)) (countLit q [-31, -32]) (countLit q [-34, -37]) (count773 q) 1 1 (meaning769 q) (meaning771 q) (meaning774 q) hs
  change valuationOf q 769 = false ∨ valuationOf q 771 = false ∨ valuationOf q 774 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause488 (q : Snake 81) (h : Conditions q) : valuation q 769 = false ∨ valuation q 771 = false ∨ valuation q 774 = true := counterClause488 (baseVal q)

theorem counterClause489 (q : Nat → Bool) : valuationOf q 773 = false ∨ valuationOf q 777 = true := by
  have hs : count777 q = (countLit q [-26, -28, -29]) + (countLit q [-31, -32, -34, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -29]) (l₂ := [-31, -32, -34, -37])
  have hm := merge_right (literal (valuationOf q) (773)) (literal (valuationOf q) (777)) (countLit q [-26, -28, -29]) (countLit q [-31, -32, -34, -37]) (count777 q) 1 (meaning773 q) (meaning777 q) hs
  change valuationOf q 773 = false ∨ valuationOf q 777 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause489 (q : Snake 81) (h : Conditions q) : valuation q 773 = false ∨ valuation q 777 = true := counterClause489 (baseVal q)

theorem counterClause490 (q : Nat → Bool) : valuationOf q 774 = false ∨ valuationOf q 778 = true := by
  have hs : count777 q = (countLit q [-26, -28, -29]) + (countLit q [-31, -32, -34, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -29]) (l₂ := [-31, -32, -34, -37])
  have hm := merge_right (literal (valuationOf q) (774)) (literal (valuationOf q) (778)) (countLit q [-26, -28, -29]) (countLit q [-31, -32, -34, -37]) (count777 q) 2 (meaning774 q) (meaning778 q) hs
  change valuationOf q 774 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause490 (q : Snake 81) (h : Conditions q) : valuation q 774 = false ∨ valuation q 778 = true := counterClause490 (baseVal q)

theorem counterClause491 (q : Nat → Bool) : valuationOf q 766 = false ∨ valuationOf q 773 = false ∨ valuationOf q 778 = true := by
  have hs : count777 q = (countLit q [-26, -28, -29]) + (countLit q [-31, -32, -34, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -29]) (l₂ := [-31, -32, -34, -37])
  have hm := merge_two (literal (valuationOf q) (766)) (literal (valuationOf q) (773)) (literal (valuationOf q) (778)) (countLit q [-26, -28, -29]) (countLit q [-31, -32, -34, -37]) (count777 q) 1 1 (meaning766 q) (meaning773 q) (meaning778 q) hs
  change valuationOf q 766 = false ∨ valuationOf q 773 = false ∨ valuationOf q 778 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause491 (q : Snake 81) (h : Conditions q) : valuation q 766 = false ∨ valuation q 773 = false ∨ valuation q 778 = true := counterClause491 (baseVal q)

theorem counterClause492 (q : Nat → Bool) : valuationOf q 767 = false ∨ valuationOf q 773 = false ∨ valuationOf q 779 = true := by
  have hs : count777 q = (countLit q [-26, -28, -29]) + (countLit q [-31, -32, -34, -37]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -29]) (l₂ := [-31, -32, -34, -37])
  have hm := merge_two (literal (valuationOf q) (767)) (literal (valuationOf q) (773)) (literal (valuationOf q) (779)) (countLit q [-26, -28, -29]) (countLit q [-31, -32, -34, -37]) (count777 q) 2 1 (meaning767 q) (meaning773 q) (meaning779 q) hs
  change valuationOf q 767 = false ∨ valuationOf q 773 = false ∨ valuationOf q 779 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause492 (q : Snake 81) (h : Conditions q) : valuation q 767 = false ∨ valuation q 773 = false ∨ valuation q 779 = true := counterClause492 (baseVal q)

theorem counterClause493 (q : Nat → Bool) : valuationOf q 41 = true ∨ valuationOf q 784 = true := by
  have hs : count784 q = (countLit q [-40]) + (countLit q [-41]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-41])
  have hm := merge_right (literal (valuationOf q) (-41)) (literal (valuationOf q) (784)) (countLit q [-40]) (countLit q [-41]) (count784 q) 1 (meaningNeg41 q) (meaning784 q) hs
  change (! (valuationOf q 41)) = false ∨ valuationOf q 784 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause493 (q : Snake 81) (h : Conditions q) : valuation q 41 = true ∨ valuation q 784 = true := counterClause493 (baseVal q)

theorem counterClause494 (q : Nat → Bool) : valuationOf q 784 = false ∨ valuationOf q 786 = true := by
  have hs : count786 q = (countLit q [-39]) + (countLit q [-40, -41]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40, -41])
  have hm := merge_right (literal (valuationOf q) (784)) (literal (valuationOf q) (786)) (countLit q [-39]) (countLit q [-40, -41]) (count786 q) 1 (meaning784 q) (meaning786 q) hs
  change valuationOf q 784 = false ∨ valuationOf q 786 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause494 (q : Snake 81) (h : Conditions q) : valuation q 784 = false ∨ valuation q 786 = true := counterClause494 (baseVal q)

theorem counterClause495 (q : Nat → Bool) : valuationOf q 47 = true ∨ valuationOf q 789 = true := by
  have hs : count789 q = (countLit q [-46]) + (countLit q [-47]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-47])
  have hm := merge_right (literal (valuationOf q) (-47)) (literal (valuationOf q) (789)) (countLit q [-46]) (countLit q [-47]) (count789 q) 1 (meaningNeg47 q) (meaning789 q) hs
  change (! (valuationOf q 47)) = false ∨ valuationOf q 789 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause495 (q : Snake 81) (h : Conditions q) : valuation q 47 = true ∨ valuation q 789 = true := counterClause495 (baseVal q)

theorem counterClause496 (q : Nat → Bool) : valuationOf q 789 = false ∨ valuationOf q 793 = true := by
  have hs : count793 q = (countLit q [-46, -47]) + (countLit q [-48, -51]) := List.countP_append (p := literal q) (l₁ := [-46, -47]) (l₂ := [-48, -51])
  have hm := merge_left (literal (valuationOf q) (789)) (literal (valuationOf q) (793)) (countLit q [-46, -47]) (countLit q [-48, -51]) (count793 q) 1 (meaning789 q) (meaning793 q) hs
  change valuationOf q 789 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause496 (q : Snake 81) (h : Conditions q) : valuation q 789 = false ∨ valuation q 793 = true := counterClause496 (baseVal q)

theorem counterClause497 (q : Nat → Bool) : valuationOf q 786 = false ∨ valuationOf q 793 = false ∨ valuationOf q 798 = true := by
  have hs : count797 q = (countLit q [-39, -40, -41]) + (countLit q [-46, -47, -48, -51]) := List.countP_append (p := literal q) (l₁ := [-39, -40, -41]) (l₂ := [-46, -47, -48, -51])
  have hm := merge_two (literal (valuationOf q) (786)) (literal (valuationOf q) (793)) (literal (valuationOf q) (798)) (countLit q [-39, -40, -41]) (countLit q [-46, -47, -48, -51]) (count797 q) 1 1 (meaning786 q) (meaning793 q) (meaning798 q) hs
  change valuationOf q 786 = false ∨ valuationOf q 793 = false ∨ valuationOf q 798 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause497 (q : Snake 81) (h : Conditions q) : valuation q 786 = false ∨ valuation q 793 = false ∨ valuation q 798 = true := counterClause497 (baseVal q)

theorem counterClause498 (q : Nat → Bool) : valuationOf q 777 = false ∨ valuationOf q 798 = false ∨ valuationOf q 806 = true := by
  have hs : count804 q = (countLit q [-26, -28, -29, -31, -32, -34, -37]) + (countLit q [-39, -40, -41, -46, -47, -48, -51]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -29, -31, -32, -34, -37]) (l₂ := [-39, -40, -41, -46, -47, -48, -51])
  have hm := merge_two (literal (valuationOf q) (777)) (literal (valuationOf q) (798)) (literal (valuationOf q) (806)) (countLit q [-26, -28, -29, -31, -32, -34, -37]) (countLit q [-39, -40, -41, -46, -47, -48, -51]) (count804 q) 1 2 (meaning777 q) (meaning798 q) (meaning806 q) hs
  change valuationOf q 777 = false ∨ valuationOf q 798 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause498 (q : Snake 81) (h : Conditions q) : valuation q 777 = false ∨ valuation q 798 = false ∨ valuation q 806 = true := counterClause498 (baseVal q)

theorem counterClause499 (q : Nat → Bool) : valuationOf q 778 = false ∨ valuationOf q 798 = false ∨ valuationOf q 807 = true := by
  have hs : count804 q = (countLit q [-26, -28, -29, -31, -32, -34, -37]) + (countLit q [-39, -40, -41, -46, -47, -48, -51]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -29, -31, -32, -34, -37]) (l₂ := [-39, -40, -41, -46, -47, -48, -51])
  have hm := merge_two (literal (valuationOf q) (778)) (literal (valuationOf q) (798)) (literal (valuationOf q) (807)) (countLit q [-26, -28, -29, -31, -32, -34, -37]) (countLit q [-39, -40, -41, -46, -47, -48, -51]) (count804 q) 2 2 (meaning778 q) (meaning798 q) (meaning807 q) hs
  change valuationOf q 778 = false ∨ valuationOf q 798 = false ∨ valuationOf q 807 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause499 (q : Snake 81) (h : Conditions q) : valuation q 778 = false ∨ valuation q 798 = false ∨ valuation q 807 = true := counterClause499 (baseVal q)

theorem counterClause500 (q : Nat → Bool) : valuationOf q 779 = false ∨ valuationOf q 806 = true := by
  have hs : count804 q = (countLit q [-26, -28, -29, -31, -32, -34, -37]) + (countLit q [-39, -40, -41, -46, -47, -48, -51]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -29, -31, -32, -34, -37]) (l₂ := [-39, -40, -41, -46, -47, -48, -51])
  have hm := merge_left (literal (valuationOf q) (779)) (literal (valuationOf q) (806)) (countLit q [-26, -28, -29, -31, -32, -34, -37]) (countLit q [-39, -40, -41, -46, -47, -48, -51]) (count804 q) 3 (meaning779 q) (meaning806 q) hs
  change valuationOf q 779 = false ∨ valuationOf q 806 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause500 (q : Snake 81) (h : Conditions q) : valuation q 779 = false ∨ valuation q 806 = true := counterClause500 (baseVal q)

theorem counterClause501 (q : Nat → Bool) : valuationOf q 779 = false ∨ valuationOf q 798 = false ∨ valuationOf q 808 = true := by
  have hs : count804 q = (countLit q [-26, -28, -29, -31, -32, -34, -37]) + (countLit q [-39, -40, -41, -46, -47, -48, -51]) := List.countP_append (p := literal q) (l₁ := [-26, -28, -29, -31, -32, -34, -37]) (l₂ := [-39, -40, -41, -46, -47, -48, -51])
  have hm := merge_two (literal (valuationOf q) (779)) (literal (valuationOf q) (798)) (literal (valuationOf q) (808)) (countLit q [-26, -28, -29, -31, -32, -34, -37]) (countLit q [-39, -40, -41, -46, -47, -48, -51]) (count804 q) 3 2 (meaning779 q) (meaning798 q) (meaning808 q) hs
  change valuationOf q 779 = false ∨ valuationOf q 798 = false ∨ valuationOf q 808 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause501 (q : Snake 81) (h : Conditions q) : valuation q 779 = false ∨ valuation q 798 = false ∨ valuation q 808 = true := counterClause501 (baseVal q)

theorem counterClause502 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 806 = false ∨ valuationOf q 827 = true := by
  have hs : count818 q = (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) + (countLit q [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) (l₂ := [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51])
  have hm := merge_two (literal (valuationOf q) (757)) (literal (valuationOf q) (806)) (literal (valuationOf q) (827)) (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) (countLit q [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (count818 q) 7 3 (meaning757 q) (meaning806 q) (meaning827 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 806 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause502 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 806 = false ∨ valuation q 827 = true := counterClause502 (baseVal q)

theorem counterClause503 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 807 = false ∨ valuationOf q 828 = true := by
  have hs : count818 q = (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) + (countLit q [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) (l₂ := [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51])
  have hm := merge_two (literal (valuationOf q) (757)) (literal (valuationOf q) (807)) (literal (valuationOf q) (828)) (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) (countLit q [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (count818 q) 7 4 (meaning757 q) (meaning807 q) (meaning828 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 807 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause503 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 807 = false ∨ valuation q 828 = true := counterClause503 (baseVal q)

theorem counterClause504 (q : Nat → Bool) : valuationOf q 757 = false ∨ valuationOf q 808 = false ∨ valuationOf q 829 = true := by
  have hs : count818 q = (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) + (countLit q [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) (l₂ := [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51])
  have hm := merge_two (literal (valuationOf q) (757)) (literal (valuationOf q) (808)) (literal (valuationOf q) (829)) (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) (countLit q [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (count818 q) 7 5 (meaning757 q) (meaning808 q) (meaning829 q) hs
  change valuationOf q 757 = false ∨ valuationOf q 808 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause504 (q : Snake 81) (h : Conditions q) : valuation q 757 = false ∨ valuation q 808 = false ∨ valuation q 829 = true := counterClause504 (baseVal q)

theorem counterClause505 (q : Nat → Bool) : valuationOf q 758 = false ∨ valuationOf q 806 = false ∨ valuationOf q 828 = true := by
  have hs : count818 q = (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) + (countLit q [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) (l₂ := [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51])
  have hm := merge_two (literal (valuationOf q) (758)) (literal (valuationOf q) (806)) (literal (valuationOf q) (828)) (countLit q [-1, -3, -4, -5, -9, -10, -12, -14, -16, -17, -19, -20, -24]) (countLit q [-26, -28, -29, -31, -32, -34, -37, -39, -40, -41, -46, -47, -48, -51]) (count818 q) 8 3 (meaning758 q) (meaning806 q) (meaning828 q) hs
  change valuationOf q 758 = false ∨ valuationOf q 806 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause505 (q : Snake 81) (h : Conditions q) : valuation q 758 = false ∨ valuation q 806 = false ∨ valuation q 828 = true := counterClause505 (baseVal q)

theorem counterClause506 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 839 = true := by
  have hs : count839 q = (countLit q [-58]) + (countLit q [-60, -63]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-60, -63])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (839)) (countLit q [-58]) (countLit q [-60, -63]) (count839 q) 1 (meaningNeg58 q) (meaning839 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause506 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 839 = true := counterClause506 (baseVal q)

theorem counterClause507 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 842 = true := by
  have hs : count842 q = (countLit q [-52, -56, -57]) + (countLit q [-58, -60, -63]) := List.countP_append (p := literal q) (l₁ := [-52, -56, -57]) (l₂ := [-58, -60, -63])
  have hm := merge_right (literal (valuationOf q) (839)) (literal (valuationOf q) (842)) (countLit q [-52, -56, -57]) (countLit q [-58, -60, -63]) (count842 q) 1 (meaning839 q) (meaning842 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause507 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 842 = true := counterClause507 (baseVal q)

theorem counterClause508 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 855 = true := by
  have hs : count855 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (855)) (countLit q [-74]) (countLit q [-76]) (count855 q) 1 (meaningNeg74 q) (meaning855 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause508 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 855 = true := counterClause508 (baseVal q)

theorem counterClause509 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 857 = true := by
  have hs : count857 q = (countLit q [-72, -73]) + (countLit q [-74, -76]) := List.countP_append (p := literal q) (l₁ := [-72, -73]) (l₂ := [-74, -76])
  have hm := merge_right (literal (valuationOf q) (855)) (literal (valuationOf q) (857)) (countLit q [-72, -73]) (countLit q [-74, -76]) (count857 q) 1 (meaning855 q) (meaning857 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause509 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 857 = true := counterClause509 (baseVal q)

theorem counterClause510 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 861 = true := by
  have hs : count861 q = (countLit q [-65, -66, -67]) + (countLit q [-72, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-65, -66, -67]) (l₂ := [-72, -73, -74, -76])
  have hm := merge_right (literal (valuationOf q) (857)) (literal (valuationOf q) (861)) (countLit q [-65, -66, -67]) (countLit q [-72, -73, -74, -76]) (count861 q) 1 (meaning857 q) (meaning861 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause510 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 861 = true := counterClause510 (baseVal q)

theorem counterClause511 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 868 = true := by
  have hs : count868 q = (countLit q [-52, -56, -57, -58, -60, -63]) + (countLit q [-65, -66, -67, -72, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -56, -57, -58, -60, -63]) (l₂ := [-65, -66, -67, -72, -73, -74, -76])
  have hm := merge_right (literal (valuationOf q) (861)) (literal (valuationOf q) (868)) (countLit q [-52, -56, -57, -58, -60, -63]) (countLit q [-65, -66, -67, -72, -73, -74, -76]) (count868 q) 1 (meaning861 q) (meaning868 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause511 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 868 = true := counterClause511 (baseVal q)

theorem counterClause512 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 861 = false ∨ valuationOf q 869 = true := by
  have hs : count868 q = (countLit q [-52, -56, -57, -58, -60, -63]) + (countLit q [-65, -66, -67, -72, -73, -74, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -56, -57, -58, -60, -63]) (l₂ := [-65, -66, -67, -72, -73, -74, -76])
  have hm := merge_two (literal (valuationOf q) (842)) (literal (valuationOf q) (861)) (literal (valuationOf q) (869)) (countLit q [-52, -56, -57, -58, -60, -63]) (countLit q [-65, -66, -67, -72, -73, -74, -76]) (count868 q) 1 1 (meaning842 q) (meaning861 q) (meaning869 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 861 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause512 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 861 = false ∨ valuation q 869 = true := counterClause512 (baseVal q)

theorem block15 (q : Snake 81) (h : Conditions q) : B112E175.Block15 (valuation q) :=
  ⟨clause481 q h, clause482 q h, clause483 q h, clause484 q h, clause485 q h, clause486 q h, clause487 q h, clause488 q h, clause489 q h, clause490 q h, clause491 q h, clause492 q h, clause493 q h, clause494 q h, clause495 q h, clause496 q h, clause497 q h, clause498 q h, clause499 q h, clause500 q h, clause501 q h, clause502 q h, clause503 q h, clause504 q h, clause505 q h, clause506 q h, clause507 q h, clause508 q h, clause509 q h, clause510 q h, clause511 q h, clause512 q h⟩

end
end Snake9.Regrowth.E112175
