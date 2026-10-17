import E112174Semantics
import B112E174Inputs
namespace Snake9.Regrowth.E112174
noncomputable section
local instance blockDec21 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause673 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-66]) + (countLit q [-67, -69]) := List.countP_append (p := literal q) (l₁ := [-66]) (l₂ := [-67, -69])
  have hm := merge_left (literal (valuationOf q) (-66)) (literal (valuationOf q) (816)) (countLit q [-66]) (countLit q [-67, -69]) (count816 q) 1 (meaningNeg66 q) (meaning816 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause673 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 816 = true := counterClause673 (baseVal q)

theorem counterClause674 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (819)) (countLit q [-73]) (countLit q [-74]) (count819 q) 1 (meaningNeg74 q) (meaning819 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause674 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 819 = true := counterClause674 (baseVal q)

theorem counterClause675 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 821 = true := by
  have hs : count821 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (821)) (countLit q [-75]) (countLit q [-77]) (count821 q) 1 (meaningNeg77 q) (meaning821 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause675 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 821 = true := counterClause675 (baseVal q)

theorem counterClause676 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 821 = true := by
  have hs : count821 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (821)) (countLit q [-75]) (countLit q [-77]) (count821 q) 1 (meaningNeg75 q) (meaning821 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause676 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 821 = true := counterClause676 (baseVal q)

theorem counterClause677 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 77 = true ∨ valuationOf q 822 = true := by
  have hs : count821 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (822)) (countLit q [-75]) (countLit q [-77]) (count821 q) 1 1 (meaningNeg75 q) (meaningNeg77 q) (meaning822 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause677 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 822 = true := counterClause677 (baseVal q)

theorem counterClause678 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 823 = true := by
  have hs : count823 q = (countLit q [-73, -74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-75, -77])
  have hm := merge_right (literal (valuationOf q) (821)) (literal (valuationOf q) (823)) (countLit q [-73, -74]) (countLit q [-75, -77]) (count823 q) 1 (meaning821 q) (meaning823 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause678 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 823 = true := counterClause678 (baseVal q)

theorem counterClause679 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 823 = true := by
  have hs : count823 q = (countLit q [-73, -74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-75, -77])
  have hm := merge_left (literal (valuationOf q) (819)) (literal (valuationOf q) (823)) (countLit q [-73, -74]) (countLit q [-75, -77]) (count823 q) 1 (meaning819 q) (meaning823 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause679 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 823 = true := counterClause679 (baseVal q)

theorem counterClause680 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 821 = false ∨ valuationOf q 824 = true := by
  have hs : count823 q = (countLit q [-73, -74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-75, -77])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (821)) (literal (valuationOf q) (824)) (countLit q [-73, -74]) (countLit q [-75, -77]) (count823 q) 1 1 (meaning819 q) (meaning821 q) (meaning824 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 821 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause680 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 821 = false ∨ valuation q 824 = true := counterClause680 (baseVal q)

theorem counterClause681 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 822 = false ∨ valuationOf q 825 = true := by
  have hs : count823 q = (countLit q [-73, -74]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-73, -74]) (l₂ := [-75, -77])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (822)) (literal (valuationOf q) (825)) (countLit q [-73, -74]) (countLit q [-75, -77]) (count823 q) 1 2 (meaning819 q) (meaning822 q) (meaning825 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 822 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause681 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 822 = false ∨ valuation q 825 = true := counterClause681 (baseVal q)

theorem counterClause682 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 827 = true := by
  have hs : count827 q = (countLit q [-66, -67, -69]) + (countLit q [-73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-66, -67, -69]) (l₂ := [-73, -74, -75, -77])
  have hm := merge_right (literal (valuationOf q) (823)) (literal (valuationOf q) (827)) (countLit q [-66, -67, -69]) (countLit q [-73, -74, -75, -77]) (count827 q) 1 (meaning823 q) (meaning827 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause682 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 827 = true := counterClause682 (baseVal q)

theorem counterClause683 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 828 = true := by
  have hs : count827 q = (countLit q [-66, -67, -69]) + (countLit q [-73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-66, -67, -69]) (l₂ := [-73, -74, -75, -77])
  have hm := merge_right (literal (valuationOf q) (824)) (literal (valuationOf q) (828)) (countLit q [-66, -67, -69]) (countLit q [-73, -74, -75, -77]) (count827 q) 2 (meaning824 q) (meaning828 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause683 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 828 = true := counterClause683 (baseVal q)

theorem counterClause684 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-66, -67, -69]) + (countLit q [-73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-66, -67, -69]) (l₂ := [-73, -74, -75, -77])
  have hm := merge_right (literal (valuationOf q) (825)) (literal (valuationOf q) (829)) (countLit q [-66, -67, -69]) (countLit q [-73, -74, -75, -77]) (count827 q) 3 (meaning825 q) (meaning829 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause684 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 829 = true := counterClause684 (baseVal q)

theorem counterClause685 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 827 = true := by
  have hs : count827 q = (countLit q [-66, -67, -69]) + (countLit q [-73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-66, -67, -69]) (l₂ := [-73, -74, -75, -77])
  have hm := merge_left (literal (valuationOf q) (816)) (literal (valuationOf q) (827)) (countLit q [-66, -67, -69]) (countLit q [-73, -74, -75, -77]) (count827 q) 1 (meaning816 q) (meaning827 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause685 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 827 = true := counterClause685 (baseVal q)

theorem counterClause686 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 823 = false ∨ valuationOf q 828 = true := by
  have hs : count827 q = (countLit q [-66, -67, -69]) + (countLit q [-73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-66, -67, -69]) (l₂ := [-73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (816)) (literal (valuationOf q) (823)) (literal (valuationOf q) (828)) (countLit q [-66, -67, -69]) (countLit q [-73, -74, -75, -77]) (count827 q) 1 1 (meaning816 q) (meaning823 q) (meaning828 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 823 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause686 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 823 = false ∨ valuation q 828 = true := counterClause686 (baseVal q)

theorem counterClause687 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 824 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-66, -67, -69]) + (countLit q [-73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-66, -67, -69]) (l₂ := [-73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (816)) (literal (valuationOf q) (824)) (literal (valuationOf q) (829)) (countLit q [-66, -67, -69]) (countLit q [-73, -74, -75, -77]) (count827 q) 1 2 (meaning816 q) (meaning824 q) (meaning829 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 824 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause687 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 824 = false ∨ valuation q 829 = true := counterClause687 (baseVal q)

theorem counterClause688 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 834 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_right (literal (valuationOf q) (827)) (literal (valuationOf q) (834)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 1 (meaning827 q) (meaning834 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause688 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 834 = true := counterClause688 (baseVal q)

theorem counterClause689 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 835 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_right (literal (valuationOf q) (828)) (literal (valuationOf q) (835)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 2 (meaning828 q) (meaning835 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause689 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 835 = true := counterClause689 (baseVal q)

theorem counterClause690 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 827 = false ∨ valuationOf q 835 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (808)) (literal (valuationOf q) (827)) (literal (valuationOf q) (835)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 1 1 (meaning808 q) (meaning827 q) (meaning835 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 827 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause690 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 827 = false ∨ valuation q 835 = true := counterClause690 (baseVal q)

theorem counterClause691 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 828 = false ∨ valuationOf q 836 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (808)) (literal (valuationOf q) (828)) (literal (valuationOf q) (836)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 1 2 (meaning808 q) (meaning828 q) (meaning836 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 828 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause691 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 828 = false ∨ valuation q 836 = true := counterClause691 (baseVal q)

theorem counterClause692 (q : Nat → Bool) : valuationOf q 808 = false ∨ valuationOf q 829 = false ∨ valuationOf q 837 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (808)) (literal (valuationOf q) (829)) (literal (valuationOf q) (837)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 1 3 (meaning808 q) (meaning829 q) (meaning837 q) hs
  change valuationOf q 808 = false ∨ valuationOf q 829 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause692 (q : Snake 81) (h : Conditions q) : valuation q 808 = false ∨ valuation q 829 = false ∨ valuation q 837 = true := counterClause692 (baseVal q)

theorem counterClause693 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 835 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_left (literal (valuationOf q) (809)) (literal (valuationOf q) (835)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 2 (meaning809 q) (meaning835 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause693 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 835 = true := counterClause693 (baseVal q)

theorem counterClause694 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 827 = false ∨ valuationOf q 836 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (827)) (literal (valuationOf q) (836)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 2 1 (meaning809 q) (meaning827 q) (meaning836 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 827 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause694 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 827 = false ∨ valuation q 836 = true := counterClause694 (baseVal q)

theorem counterClause695 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 828 = false ∨ valuationOf q 837 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (828)) (literal (valuationOf q) (837)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 2 2 (meaning809 q) (meaning828 q) (meaning837 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 828 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause695 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 828 = false ∨ valuation q 837 = true := counterClause695 (baseVal q)

theorem counterClause696 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 829 = false ∨ valuationOf q 838 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (829)) (literal (valuationOf q) (838)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 2 3 (meaning809 q) (meaning829 q) (meaning838 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 829 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause696 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 829 = false ∨ valuation q 838 = true := counterClause696 (baseVal q)

theorem counterClause697 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 827 = false ∨ valuationOf q 837 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (827)) (literal (valuationOf q) (837)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 3 1 (meaning810 q) (meaning827 q) (meaning837 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 827 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause697 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 827 = false ∨ valuation q 837 = true := counterClause697 (baseVal q)

theorem counterClause698 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 837 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_left (literal (valuationOf q) (811)) (literal (valuationOf q) (837)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 4 (meaning811 q) (meaning837 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 837 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause698 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 837 = true := counterClause698 (baseVal q)

theorem counterClause699 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 827 = false ∨ valuationOf q 838 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (827)) (literal (valuationOf q) (838)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 4 1 (meaning811 q) (meaning827 q) (meaning838 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 827 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause699 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 827 = false ∨ valuation q 838 = true := counterClause699 (baseVal q)

theorem counterClause700 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 828 = false ∨ valuationOf q 839 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (828)) (literal (valuationOf q) (839)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 4 2 (meaning811 q) (meaning828 q) (meaning839 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 828 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause700 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 828 = false ∨ valuation q 839 = true := counterClause700 (baseVal q)

theorem counterClause701 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 838 = true := by
  have hs : count834 q = (countLit q [-53, -56, -58, -59, -61, -64]) + (countLit q [-66, -67, -69, -73, -74, -75, -77]) := List.countP_append (p := literal q) (l₁ := [-53, -56, -58, -59, -61, -64]) (l₂ := [-66, -67, -69, -73, -74, -75, -77])
  have hm := merge_left (literal (valuationOf q) (812)) (literal (valuationOf q) (838)) (countLit q [-53, -56, -58, -59, -61, -64]) (countLit q [-66, -67, -69, -73, -74, -75, -77]) (count834 q) 5 (meaning812 q) (meaning838 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause701 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 838 = true := counterClause701 (baseVal q)

theorem counterClause702 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 845 = true := by
  have hs : count845 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (845)) (countLit q [-82]) (countLit q [-84]) (count845 q) 1 (meaningNeg82 q) (meaning845 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause702 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 845 = true := counterClause702 (baseVal q)

theorem counterClause703 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 847 = true := by
  have hs : count847 q = (countLit q [-81]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -84])
  have hm := merge_right (literal (valuationOf q) (845)) (literal (valuationOf q) (847)) (countLit q [-81]) (countLit q [-82, -84]) (count847 q) 1 (meaning845 q) (meaning847 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause703 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 847 = true := counterClause703 (baseVal q)

theorem counterClause704 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 847 = true := by
  have hs : count847 q = (countLit q [-81]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -84])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (847)) (countLit q [-81]) (countLit q [-82, -84]) (count847 q) 1 (meaningNeg81 q) (meaning847 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause704 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 847 = true := counterClause704 (baseVal q)

theorem block21 (q : Snake 81) (h : Conditions q) : B112E174.Block21 (valuation q) :=
  ⟨clause673 q h, clause674 q h, clause675 q h, clause676 q h, clause677 q h, clause678 q h, clause679 q h, clause680 q h, clause681 q h, clause682 q h, clause683 q h, clause684 q h, clause685 q h, clause686 q h, clause687 q h, clause688 q h, clause689 q h, clause690 q h, clause691 q h, clause692 q h, clause693 q h, clause694 q h, clause695 q h, clause696 q h, clause697 q h, clause698 q h, clause699 q h, clause700 q h, clause701 q h, clause702 q h, clause703 q h, clause704 q h⟩

end
end Snake9.Regrowth.E112174
