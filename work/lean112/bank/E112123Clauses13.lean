import E112123Semantics
import B112E123Inputs
namespace Snake9.Regrowth.E112123
noncomputable section
local instance blockDec13 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause417 (q : Nat → Bool) : valuationOf q 787 = false ∨ valuationOf q 791 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_right (literal (valuationOf q) (787)) (literal (valuationOf q) (791)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 2 (meaning787 q) (meaning791 q) hs
  change valuationOf q 787 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause417 (q : Snake 81) (h : Conditions q) : valuation q 787 = false ∨ valuation q 791 = true := counterClause417 (baseVal q)

theorem counterClause418 (q : Nat → Bool) : valuationOf q 788 = false ∨ valuationOf q 792 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_right (literal (valuationOf q) (788)) (literal (valuationOf q) (792)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 3 (meaning788 q) (meaning792 q) hs
  change valuationOf q 788 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause418 (q : Snake 81) (h : Conditions q) : valuation q 788 = false ∨ valuation q 792 = true := counterClause418 (baseVal q)

theorem counterClause419 (q : Nat → Bool) : valuationOf q 779 = false ∨ valuationOf q 786 = false ∨ valuationOf q 791 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (779)) (literal (valuationOf q) (786)) (literal (valuationOf q) (791)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 1 1 (meaning779 q) (meaning786 q) (meaning791 q) hs
  change valuationOf q 779 = false ∨ valuationOf q 786 = false ∨ valuationOf q 791 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause419 (q : Snake 81) (h : Conditions q) : valuation q 779 = false ∨ valuation q 786 = false ∨ valuation q 791 = true := counterClause419 (baseVal q)

theorem counterClause420 (q : Nat → Bool) : valuationOf q 779 = false ∨ valuationOf q 787 = false ∨ valuationOf q 792 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (779)) (literal (valuationOf q) (787)) (literal (valuationOf q) (792)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 1 2 (meaning779 q) (meaning787 q) (meaning792 q) hs
  change valuationOf q 779 = false ∨ valuationOf q 787 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause420 (q : Snake 81) (h : Conditions q) : valuation q 779 = false ∨ valuation q 787 = false ∨ valuation q 792 = true := counterClause420 (baseVal q)

theorem counterClause421 (q : Nat → Bool) : valuationOf q 779 = false ∨ valuationOf q 788 = false ∨ valuationOf q 793 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (779)) (literal (valuationOf q) (788)) (literal (valuationOf q) (793)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 1 3 (meaning779 q) (meaning788 q) (meaning793 q) hs
  change valuationOf q 779 = false ∨ valuationOf q 788 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause421 (q : Snake 81) (h : Conditions q) : valuation q 779 = false ∨ valuation q 788 = false ∨ valuation q 793 = true := counterClause421 (baseVal q)

theorem counterClause422 (q : Nat → Bool) : valuationOf q 779 = false ∨ valuationOf q 789 = false ∨ valuationOf q 794 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (779)) (literal (valuationOf q) (789)) (literal (valuationOf q) (794)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 1 4 (meaning779 q) (meaning789 q) (meaning794 q) hs
  change valuationOf q 779 = false ∨ valuationOf q 789 = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause422 (q : Snake 81) (h : Conditions q) : valuation q 779 = false ∨ valuation q 789 = false ∨ valuation q 794 = true := counterClause422 (baseVal q)

theorem counterClause423 (q : Nat → Bool) : valuationOf q 780 = false ∨ valuationOf q 786 = false ∨ valuationOf q 792 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (780)) (literal (valuationOf q) (786)) (literal (valuationOf q) (792)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 2 1 (meaning780 q) (meaning786 q) (meaning792 q) hs
  change valuationOf q 780 = false ∨ valuationOf q 786 = false ∨ valuationOf q 792 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause423 (q : Snake 81) (h : Conditions q) : valuation q 780 = false ∨ valuation q 786 = false ∨ valuation q 792 = true := counterClause423 (baseVal q)

theorem counterClause424 (q : Nat → Bool) : valuationOf q 780 = false ∨ valuationOf q 787 = false ∨ valuationOf q 793 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (780)) (literal (valuationOf q) (787)) (literal (valuationOf q) (793)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 2 2 (meaning780 q) (meaning787 q) (meaning793 q) hs
  change valuationOf q 780 = false ∨ valuationOf q 787 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause424 (q : Snake 81) (h : Conditions q) : valuation q 780 = false ∨ valuation q 787 = false ∨ valuation q 793 = true := counterClause424 (baseVal q)

theorem counterClause425 (q : Nat → Bool) : valuationOf q 780 = false ∨ valuationOf q 788 = false ∨ valuationOf q 794 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (780)) (literal (valuationOf q) (788)) (literal (valuationOf q) (794)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 2 3 (meaning780 q) (meaning788 q) (meaning794 q) hs
  change valuationOf q 780 = false ∨ valuationOf q 788 = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause425 (q : Snake 81) (h : Conditions q) : valuation q 780 = false ∨ valuation q 788 = false ∨ valuation q 794 = true := counterClause425 (baseVal q)

theorem counterClause426 (q : Nat → Bool) : valuationOf q 780 = false ∨ valuationOf q 789 = false ∨ valuationOf q 795 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (780)) (literal (valuationOf q) (789)) (literal (valuationOf q) (795)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 2 4 (meaning780 q) (meaning789 q) (meaning795 q) hs
  change valuationOf q 780 = false ∨ valuationOf q 789 = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause426 (q : Snake 81) (h : Conditions q) : valuation q 780 = false ∨ valuation q 789 = false ∨ valuation q 795 = true := counterClause426 (baseVal q)

theorem counterClause427 (q : Nat → Bool) : valuationOf q 781 = false ∨ valuationOf q 786 = false ∨ valuationOf q 793 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (781)) (literal (valuationOf q) (786)) (literal (valuationOf q) (793)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 3 1 (meaning781 q) (meaning786 q) (meaning793 q) hs
  change valuationOf q 781 = false ∨ valuationOf q 786 = false ∨ valuationOf q 793 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause427 (q : Snake 81) (h : Conditions q) : valuation q 781 = false ∨ valuation q 786 = false ∨ valuation q 793 = true := counterClause427 (baseVal q)

theorem counterClause428 (q : Nat → Bool) : valuationOf q 781 = false ∨ valuationOf q 787 = false ∨ valuationOf q 794 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (781)) (literal (valuationOf q) (787)) (literal (valuationOf q) (794)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 3 2 (meaning781 q) (meaning787 q) (meaning794 q) hs
  change valuationOf q 781 = false ∨ valuationOf q 787 = false ∨ valuationOf q 794 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause428 (q : Snake 81) (h : Conditions q) : valuation q 781 = false ∨ valuation q 787 = false ∨ valuation q 794 = true := counterClause428 (baseVal q)

theorem counterClause429 (q : Nat → Bool) : valuationOf q 781 = false ∨ valuationOf q 788 = false ∨ valuationOf q 795 = true := by
  have hs : count790 q = (countLit q [-15, -17, -18]) + (countLit q [-20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (781)) (literal (valuationOf q) (788)) (literal (valuationOf q) (795)) (countLit q [-15, -17, -18]) (countLit q [-20, -21, -24, -25]) (count790 q) 3 3 (meaning781 q) (meaning788 q) (meaning795 q) hs
  change valuationOf q 781 = false ∨ valuationOf q 788 = false ∨ valuationOf q 795 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause429 (q : Snake 81) (h : Conditions q) : valuation q 781 = false ∨ valuation q 788 = false ∨ valuation q 795 = true := counterClause429 (baseVal q)

theorem counterClause430 (q : Nat → Bool) : valuationOf q 770 = false ∨ valuationOf q 794 = false ∨ valuationOf q 802 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (770)) (literal (valuationOf q) (794)) (literal (valuationOf q) (802)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 1 5 (meaning770 q) (meaning794 q) (meaning802 q) hs
  change valuationOf q 770 = false ∨ valuationOf q 794 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause430 (q : Snake 81) (h : Conditions q) : valuation q 770 = false ∨ valuation q 794 = false ∨ valuation q 802 = true := counterClause430 (baseVal q)

theorem counterClause431 (q : Nat → Bool) : valuationOf q 771 = false ∨ valuationOf q 792 = false ∨ valuationOf q 801 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (771)) (literal (valuationOf q) (792)) (literal (valuationOf q) (801)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 2 3 (meaning771 q) (meaning792 q) (meaning801 q) hs
  change valuationOf q 771 = false ∨ valuationOf q 792 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause431 (q : Snake 81) (h : Conditions q) : valuation q 771 = false ∨ valuation q 792 = false ∨ valuation q 801 = true := counterClause431 (baseVal q)

theorem counterClause432 (q : Nat → Bool) : valuationOf q 771 = false ∨ valuationOf q 793 = false ∨ valuationOf q 802 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (771)) (literal (valuationOf q) (793)) (literal (valuationOf q) (802)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 2 4 (meaning771 q) (meaning793 q) (meaning802 q) hs
  change valuationOf q 771 = false ∨ valuationOf q 793 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause432 (q : Snake 81) (h : Conditions q) : valuation q 771 = false ∨ valuation q 793 = false ∨ valuation q 802 = true := counterClause432 (baseVal q)

theorem counterClause433 (q : Nat → Bool) : valuationOf q 771 = false ∨ valuationOf q 794 = false ∨ valuationOf q 803 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (771)) (literal (valuationOf q) (794)) (literal (valuationOf q) (803)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 2 5 (meaning771 q) (meaning794 q) (meaning803 q) hs
  change valuationOf q 771 = false ∨ valuationOf q 794 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause433 (q : Snake 81) (h : Conditions q) : valuation q 771 = false ∨ valuation q 794 = false ∨ valuation q 803 = true := counterClause433 (baseVal q)

theorem counterClause434 (q : Nat → Bool) : valuationOf q 771 = false ∨ valuationOf q 795 = false ∨ valuationOf q 804 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (771)) (literal (valuationOf q) (795)) (literal (valuationOf q) (804)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 2 6 (meaning771 q) (meaning795 q) (meaning804 q) hs
  change valuationOf q 771 = false ∨ valuationOf q 795 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause434 (q : Snake 81) (h : Conditions q) : valuation q 771 = false ∨ valuation q 795 = false ∨ valuation q 804 = true := counterClause434 (baseVal q)

theorem counterClause435 (q : Nat → Bool) : valuationOf q 772 = false ∨ valuationOf q 791 = false ∨ valuationOf q 801 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (772)) (literal (valuationOf q) (791)) (literal (valuationOf q) (801)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 3 2 (meaning772 q) (meaning791 q) (meaning801 q) hs
  change valuationOf q 772 = false ∨ valuationOf q 791 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause435 (q : Snake 81) (h : Conditions q) : valuation q 772 = false ∨ valuation q 791 = false ∨ valuation q 801 = true := counterClause435 (baseVal q)

theorem counterClause436 (q : Nat → Bool) : valuationOf q 772 = false ∨ valuationOf q 792 = false ∨ valuationOf q 802 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (772)) (literal (valuationOf q) (792)) (literal (valuationOf q) (802)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 3 3 (meaning772 q) (meaning792 q) (meaning802 q) hs
  change valuationOf q 772 = false ∨ valuationOf q 792 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause436 (q : Snake 81) (h : Conditions q) : valuation q 772 = false ∨ valuation q 792 = false ∨ valuation q 802 = true := counterClause436 (baseVal q)

theorem counterClause437 (q : Nat → Bool) : valuationOf q 772 = false ∨ valuationOf q 793 = false ∨ valuationOf q 803 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (772)) (literal (valuationOf q) (793)) (literal (valuationOf q) (803)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 3 4 (meaning772 q) (meaning793 q) (meaning803 q) hs
  change valuationOf q 772 = false ∨ valuationOf q 793 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause437 (q : Snake 81) (h : Conditions q) : valuation q 772 = false ∨ valuation q 793 = false ∨ valuation q 803 = true := counterClause437 (baseVal q)

theorem counterClause438 (q : Nat → Bool) : valuationOf q 772 = false ∨ valuationOf q 794 = false ∨ valuationOf q 804 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (772)) (literal (valuationOf q) (794)) (literal (valuationOf q) (804)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 3 5 (meaning772 q) (meaning794 q) (meaning804 q) hs
  change valuationOf q 772 = false ∨ valuationOf q 794 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause438 (q : Snake 81) (h : Conditions q) : valuation q 772 = false ∨ valuation q 794 = false ∨ valuation q 804 = true := counterClause438 (baseVal q)

theorem counterClause439 (q : Nat → Bool) : valuationOf q 773 = false ∨ valuationOf q 790 = false ∨ valuationOf q 801 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (773)) (literal (valuationOf q) (790)) (literal (valuationOf q) (801)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 4 1 (meaning773 q) (meaning790 q) (meaning801 q) hs
  change valuationOf q 773 = false ∨ valuationOf q 790 = false ∨ valuationOf q 801 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause439 (q : Snake 81) (h : Conditions q) : valuation q 773 = false ∨ valuation q 790 = false ∨ valuation q 801 = true := counterClause439 (baseVal q)

theorem counterClause440 (q : Nat → Bool) : valuationOf q 773 = false ∨ valuationOf q 791 = false ∨ valuationOf q 802 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (773)) (literal (valuationOf q) (791)) (literal (valuationOf q) (802)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 4 2 (meaning773 q) (meaning791 q) (meaning802 q) hs
  change valuationOf q 773 = false ∨ valuationOf q 791 = false ∨ valuationOf q 802 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause440 (q : Snake 81) (h : Conditions q) : valuation q 773 = false ∨ valuation q 791 = false ∨ valuation q 802 = true := counterClause440 (baseVal q)

theorem counterClause441 (q : Nat → Bool) : valuationOf q 773 = false ∨ valuationOf q 792 = false ∨ valuationOf q 803 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (773)) (literal (valuationOf q) (792)) (literal (valuationOf q) (803)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 4 3 (meaning773 q) (meaning792 q) (meaning803 q) hs
  change valuationOf q 773 = false ∨ valuationOf q 792 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause441 (q : Snake 81) (h : Conditions q) : valuation q 773 = false ∨ valuation q 792 = false ∨ valuation q 803 = true := counterClause441 (baseVal q)

theorem counterClause442 (q : Nat → Bool) : valuationOf q 773 = false ∨ valuationOf q 793 = false ∨ valuationOf q 804 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (773)) (literal (valuationOf q) (793)) (literal (valuationOf q) (804)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 4 4 (meaning773 q) (meaning793 q) (meaning804 q) hs
  change valuationOf q 773 = false ∨ valuationOf q 793 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause442 (q : Snake 81) (h : Conditions q) : valuation q 773 = false ∨ valuation q 793 = false ∨ valuation q 804 = true := counterClause442 (baseVal q)

theorem counterClause443 (q : Nat → Bool) : valuationOf q 774 = false ∨ valuationOf q 791 = false ∨ valuationOf q 803 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (774)) (literal (valuationOf q) (791)) (literal (valuationOf q) (803)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 5 2 (meaning774 q) (meaning791 q) (meaning803 q) hs
  change valuationOf q 774 = false ∨ valuationOf q 791 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause443 (q : Snake 81) (h : Conditions q) : valuation q 774 = false ∨ valuation q 791 = false ∨ valuation q 803 = true := counterClause443 (baseVal q)

theorem counterClause444 (q : Nat → Bool) : valuationOf q 774 = false ∨ valuationOf q 792 = false ∨ valuationOf q 804 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (774)) (literal (valuationOf q) (792)) (literal (valuationOf q) (804)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 5 3 (meaning774 q) (meaning792 q) (meaning804 q) hs
  change valuationOf q 774 = false ∨ valuationOf q 792 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause444 (q : Snake 81) (h : Conditions q) : valuation q 774 = false ∨ valuation q 792 = false ∨ valuation q 804 = true := counterClause444 (baseVal q)

theorem counterClause445 (q : Nat → Bool) : valuationOf q 774 = false ∨ valuationOf q 793 = false ∨ valuationOf q 805 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (774)) (literal (valuationOf q) (793)) (literal (valuationOf q) (805)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 5 4 (meaning774 q) (meaning793 q) (meaning805 q) hs
  change valuationOf q 774 = false ∨ valuationOf q 793 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause445 (q : Snake 81) (h : Conditions q) : valuation q 774 = false ∨ valuation q 793 = false ∨ valuation q 805 = true := counterClause445 (baseVal q)

theorem counterClause446 (q : Nat → Bool) : valuationOf q 775 = false ∨ valuationOf q 790 = false ∨ valuationOf q 803 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (775)) (literal (valuationOf q) (790)) (literal (valuationOf q) (803)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 6 1 (meaning775 q) (meaning790 q) (meaning803 q) hs
  change valuationOf q 775 = false ∨ valuationOf q 790 = false ∨ valuationOf q 803 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause446 (q : Snake 81) (h : Conditions q) : valuation q 775 = false ∨ valuation q 790 = false ∨ valuation q 803 = true := counterClause446 (baseVal q)

theorem counterClause447 (q : Nat → Bool) : valuationOf q 775 = false ∨ valuationOf q 791 = false ∨ valuationOf q 804 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (775)) (literal (valuationOf q) (791)) (literal (valuationOf q) (804)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 6 2 (meaning775 q) (meaning791 q) (meaning804 q) hs
  change valuationOf q 775 = false ∨ valuationOf q 791 = false ∨ valuationOf q 804 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause447 (q : Snake 81) (h : Conditions q) : valuation q 775 = false ∨ valuation q 791 = false ∨ valuation q 804 = true := counterClause447 (baseVal q)

theorem counterClause448 (q : Nat → Bool) : valuationOf q 775 = false ∨ valuationOf q 792 = false ∨ valuationOf q 805 = true := by
  have hs : count797 q = (countLit q [-1, -4, -5, -6, -9, -11, -12]) + (countLit q [-15, -17, -18, -20, -21, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -5, -6, -9, -11, -12]) (l₂ := [-15, -17, -18, -20, -21, -24, -25])
  have hm := merge_two (literal (valuationOf q) (775)) (literal (valuationOf q) (792)) (literal (valuationOf q) (805)) (countLit q [-1, -4, -5, -6, -9, -11, -12]) (countLit q [-15, -17, -18, -20, -21, -24, -25]) (count797 q) 6 3 (meaning775 q) (meaning792 q) (meaning805 q) hs
  change valuationOf q 775 = false ∨ valuationOf q 792 = false ∨ valuationOf q 805 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause448 (q : Snake 81) (h : Conditions q) : valuation q 775 = false ∨ valuation q 792 = false ∨ valuation q 805 = true := counterClause448 (baseVal q)

theorem block13 (q : Snake 81) (h : Conditions q) : B112E123.Block13 (valuation q) :=
  ⟨clause417 q h, clause418 q h, clause419 q h, clause420 q h, clause421 q h, clause422 q h, clause423 q h, clause424 q h, clause425 q h, clause426 q h, clause427 q h, clause428 q h, clause429 q h, clause430 q h, clause431 q h, clause432 q h, clause433 q h, clause434 q h, clause435 q h, clause436 q h, clause437 q h, clause438 q h, clause439 q h, clause440 q h, clause441 q h, clause442 q h, clause443 q h, clause444 q h, clause445 q h, clause446 q h, clause447 q h, clause448 q h⟩

end
end Snake9.Regrowth.E112123
