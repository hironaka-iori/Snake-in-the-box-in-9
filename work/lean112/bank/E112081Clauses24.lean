import E112081Semantics
import B112E081Inputs
namespace Snake9.Regrowth.E112081
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-21, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (825)) (literal (valuationOf q) (827)) (countLit q [-21, -25]) (countLit q [-27, -29]) (count826 q) 2 (meaning825 q) (meaning827 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 827 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-21, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (822)) (literal (valuationOf q) (826)) (countLit q [-21, -25]) (countLit q [-27, -29]) (count826 q) 1 (meaning822 q) (meaning826 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 826 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-21, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (824)) (literal (valuationOf q) (827)) (countLit q [-21, -25]) (countLit q [-27, -29]) (count826 q) 1 1 (meaning822 q) (meaning824 q) (meaning827 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 824 = false ∨ valuation q 827 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 825 = false ∨ valuationOf q 828 = true := by
  have hs : count826 q = (countLit q [-21, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (825)) (literal (valuationOf q) (828)) (countLit q [-21, -25]) (countLit q [-27, -29]) (count826 q) 1 2 (meaning822 q) (meaning825 q) (meaning828 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 825 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 825 = false ∨ valuation q 828 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-21, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (823)) (literal (valuationOf q) (827)) (countLit q [-21, -25]) (countLit q [-27, -29]) (count826 q) 2 (meaning823 q) (meaning827 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 827 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 824 = false ∨ valuationOf q 828 = true := by
  have hs : count826 q = (countLit q [-21, -25]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -25]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (824)) (literal (valuationOf q) (828)) (countLit q [-21, -25]) (countLit q [-27, -29]) (count826 q) 2 1 (meaning823 q) (meaning824 q) (meaning828 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 824 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 824 = false ∨ valuation q 828 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (826)) (literal (valuationOf q) (830)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 1 (meaning826 q) (meaning830 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 830 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (827)) (literal (valuationOf q) (831)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 2 (meaning827 q) (meaning831 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 831 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_right (literal (valuationOf q) (828)) (literal (valuationOf q) (832)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 3 (meaning828 q) (meaning832 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 832 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (819)) (literal (valuationOf q) (830)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 1 (meaning819 q) (meaning830 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 830 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 826 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (826)) (literal (valuationOf q) (831)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 1 1 (meaning819 q) (meaning826 q) (meaning831 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 826 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 826 = false ∨ valuation q 831 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 827 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (827)) (literal (valuationOf q) (832)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 1 2 (meaning819 q) (meaning827 q) (meaning832 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 827 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 827 = false ∨ valuation q 832 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 828 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (828)) (literal (valuationOf q) (833)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 1 3 (meaning819 q) (meaning828 q) (meaning833 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 828 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 828 = false ∨ valuation q 833 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (820)) (literal (valuationOf q) (831)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 2 (meaning820 q) (meaning831 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 831 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 826 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (820)) (literal (valuationOf q) (826)) (literal (valuationOf q) (832)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 2 1 (meaning820 q) (meaning826 q) (meaning832 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 826 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 826 = false ∨ valuation q 832 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 827 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (820)) (literal (valuationOf q) (827)) (literal (valuationOf q) (833)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 2 2 (meaning820 q) (meaning827 q) (meaning833 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 827 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 827 = false ∨ valuation q 833 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 828 = false ∨ valuationOf q 834 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (820)) (literal (valuationOf q) (828)) (literal (valuationOf q) (834)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 2 3 (meaning820 q) (meaning828 q) (meaning834 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 828 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 828 = false ∨ valuation q 834 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (821)) (literal (valuationOf q) (832)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 3 (meaning821 q) (meaning832 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 832 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 826 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (821)) (literal (valuationOf q) (826)) (literal (valuationOf q) (833)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 3 1 (meaning821 q) (meaning826 q) (meaning833 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 826 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 826 = false ∨ valuation q 833 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 827 = false ∨ valuationOf q 834 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (821)) (literal (valuationOf q) (827)) (literal (valuationOf q) (834)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 3 2 (meaning821 q) (meaning827 q) (meaning834 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 827 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 827 = false ∨ valuation q 834 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 828 = false ∨ valuationOf q 835 = true := by
  have hs : count830 q = (countLit q [-17, -18, -20]) + (countLit q [-21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -20]) (l₂ := [-21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (821)) (literal (valuationOf q) (828)) (literal (valuationOf q) (835)) (countLit q [-17, -18, -20]) (countLit q [-21, -25, -27, -29]) (count830 q) 3 3 (meaning821 q) (meaning828 q) (meaning835 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 828 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 828 = false ∨ valuation q 835 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 830 = false ∨ valuationOf q 838 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (830)) (literal (valuationOf q) (838)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 1 1 (meaning810 q) (meaning830 q) (meaning838 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 830 = false ∨ valuationOf q 838 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 830 = false ∨ valuation q 838 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 831 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (831)) (literal (valuationOf q) (839)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 1 2 (meaning810 q) (meaning831 q) (meaning839 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 831 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 831 = false ∨ valuation q 839 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 832 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (832)) (literal (valuationOf q) (840)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 1 3 (meaning810 q) (meaning832 q) (meaning840 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 832 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 832 = false ∨ valuation q 840 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 833 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (833)) (literal (valuationOf q) (841)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 1 4 (meaning810 q) (meaning833 q) (meaning841 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 833 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 833 = false ∨ valuation q 841 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 834 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (834)) (literal (valuationOf q) (842)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 1 5 (meaning810 q) (meaning834 q) (meaning842 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 834 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 834 = false ∨ valuation q 842 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 835 = false ∨ valuationOf q 843 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (835)) (literal (valuationOf q) (843)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 1 6 (meaning810 q) (meaning835 q) (meaning843 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 835 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 835 = false ∨ valuation q 843 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 831 = false ∨ valuationOf q 840 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (831)) (literal (valuationOf q) (840)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 2 2 (meaning811 q) (meaning831 q) (meaning840 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 831 = false ∨ valuationOf q 840 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 831 = false ∨ valuation q 840 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 832 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (832)) (literal (valuationOf q) (841)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 2 3 (meaning811 q) (meaning832 q) (meaning841 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 832 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 832 = false ∨ valuation q 841 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 833 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (833)) (literal (valuationOf q) (842)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 2 4 (meaning811 q) (meaning833 q) (meaning842 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 833 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 833 = false ∨ valuation q 842 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 834 = false ∨ valuationOf q 843 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (834)) (literal (valuationOf q) (843)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 2 5 (meaning811 q) (meaning834 q) (meaning843 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 834 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 834 = false ∨ valuation q 843 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 839 = true := by
  have hs : count837 q = (countLit q [-1, -3, -7, -9, -10, -14, -15]) + (countLit q [-17, -18, -20, -21, -25, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -7, -9, -10, -14, -15]) (l₂ := [-17, -18, -20, -21, -25, -27, -29])
  have hm := merge_left (literal (valuationOf q) (812)) (literal (valuationOf q) (839)) (countLit q [-1, -3, -7, -9, -10, -14, -15]) (countLit q [-17, -18, -20, -21, -25, -27, -29]) (count837 q) 3 (meaning812 q) (meaning839 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 839 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 839 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E081.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112081
