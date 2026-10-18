import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 801 = false ∨ valuationOf q 809 = false ∨ valuationOf q 816 = true := by
  have hs : count810 q = (countLit q [-1, -4, -7]) + (countLit q [-9, -11, -13, -14]) := List.countP_append (p := literal q) (l₁ := [-1, -4, -7]) (l₂ := [-9, -11, -13, -14])
  have hm := merge_two (literal (valuationOf q) (801)) (literal (valuationOf q) (809)) (literal (valuationOf q) (816)) (countLit q [-1, -4, -7]) (countLit q [-9, -11, -13, -14]) (count810 q) 3 4 (meaning801 q) (meaning809 q) (meaning816 q) hs
  change valuationOf q 801 = false ∨ valuationOf q 809 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 801 = false ∨ valuation q 809 = false ∨ valuation q 816 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 817 = true := by
  have hs : count817 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (817)) (countLit q [-18]) (countLit q [-19]) (count817 q) 1 (meaningNeg19 q) (meaning817 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 817 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 817 = true := by
  have hs : count817 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (817)) (countLit q [-18]) (countLit q [-19]) (count817 q) 1 (meaningNeg18 q) (meaning817 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 817 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 19 = true ∨ valuationOf q 818 = true := by
  have hs : count817 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (818)) (countLit q [-18]) (countLit q [-19]) (count817 q) 1 1 (meaningNeg18 q) (meaningNeg19 q) (meaning818 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 818 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (817)) (literal (valuationOf q) (819)) (countLit q [-16]) (countLit q [-18, -19]) (count819 q) 1 (meaning817 q) (meaning819 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 819 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (818)) (literal (valuationOf q) (820)) (countLit q [-16]) (countLit q [-18, -19]) (count819 q) 2 (meaning818 q) (meaning820 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 820 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 819 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18, -19])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (819)) (countLit q [-16]) (countLit q [-18, -19]) (count819 q) 1 (meaningNeg16 q) (meaning819 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 819 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (817)) (literal (valuationOf q) (820)) (countLit q [-16]) (countLit q [-18, -19]) (count819 q) 1 1 (meaningNeg16 q) (meaning817 q) (meaning820 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 817 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 817 = false ∨ valuation q 820 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 818 = false ∨ valuationOf q 821 = true := by
  have hs : count819 q = (countLit q [-16]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18, -19])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (818)) (literal (valuationOf q) (821)) (countLit q [-16]) (countLit q [-18, -19]) (count819 q) 1 2 (meaningNeg16 q) (meaning818 q) (meaning821 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 818 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 818 = false ∨ valuation q 821 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 822 = true := by
  have hs : count822 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (822)) (countLit q [-21]) (countLit q [-22]) (count822 q) 1 (meaningNeg22 q) (meaning822 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 822 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 822 = true := by
  have hs : count822 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (822)) (countLit q [-21]) (countLit q [-22]) (count822 q) 1 (meaningNeg21 q) (meaning822 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 822 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 22 = true ∨ valuationOf q 823 = true := by
  have hs : count822 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (823)) (countLit q [-21]) (countLit q [-22]) (count822 q) 1 1 (meaningNeg21 q) (meaningNeg22 q) (meaning823 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 22 = true ∨ valuation q 823 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 824 = true := by
  have hs : count824 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (824)) (countLit q [-24]) (countLit q [-25]) (count824 q) 1 (meaningNeg25 q) (meaning824 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 824 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 824 = true := by
  have hs : count824 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (824)) (countLit q [-24]) (countLit q [-25]) (count824 q) 1 (meaningNeg24 q) (meaning824 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 824 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 25 = true ∨ valuationOf q 825 = true := by
  have hs : count824 q = (countLit q [-24]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (825)) (countLit q [-24]) (countLit q [-25]) (count824 q) 1 1 (meaningNeg24 q) (meaningNeg25 q) (meaning825 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 25 = true ∨ valuation q 825 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (824)) (literal (valuationOf q) (826)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 1 (meaning824 q) (meaning826 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 826 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 825 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_right (literal (valuationOf q) (825)) (literal (valuationOf q) (827)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 2 (meaning825 q) (meaning827 q) hs
  change valuationOf q 825 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 825 = false ∨ valuation q 827 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 826 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_left (literal (valuationOf q) (822)) (literal (valuationOf q) (826)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 1 (meaning822 q) (meaning826 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 826 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 826 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (824)) (literal (valuationOf q) (827)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 1 1 (meaning822 q) (meaning824 q) (meaning827 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 824 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 824 = false ∨ valuation q 827 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 825 = false ∨ valuationOf q 828 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (822)) (literal (valuationOf q) (825)) (literal (valuationOf q) (828)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 1 2 (meaning822 q) (meaning825 q) (meaning828 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 825 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 825 = false ∨ valuation q 828 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 827 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_left (literal (valuationOf q) (823)) (literal (valuationOf q) (827)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 2 (meaning823 q) (meaning827 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 827 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 824 = false ∨ valuationOf q 828 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (824)) (literal (valuationOf q) (828)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 2 1 (meaning823 q) (meaning824 q) (meaning828 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 824 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 824 = false ∨ valuation q 828 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 825 = false ∨ valuationOf q 829 = true := by
  have hs : count826 q = (countLit q [-21, -22]) + (countLit q [-24, -25]) := List.countP_append (p := literal q) (l₁ := [-21, -22]) (l₂ := [-24, -25])
  have hm := merge_two (literal (valuationOf q) (823)) (literal (valuationOf q) (825)) (literal (valuationOf q) (829)) (countLit q [-21, -22]) (countLit q [-24, -25]) (count826 q) 2 2 (meaning823 q) (meaning825 q) (meaning829 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 825 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 825 = false ∨ valuation q 829 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 826 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (826)) (literal (valuationOf q) (830)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 1 (meaning826 q) (meaning830 q) hs
  change valuationOf q 826 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 826 = false ∨ valuation q 830 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 827 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (827)) (literal (valuationOf q) (831)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 2 (meaning827 q) (meaning831 q) hs
  change valuationOf q 827 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 827 = false ∨ valuation q 831 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 828 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_right (literal (valuationOf q) (828)) (literal (valuationOf q) (832)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 3 (meaning828 q) (meaning832 q) hs
  change valuationOf q 828 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 828 = false ∨ valuation q 832 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 830 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (819)) (literal (valuationOf q) (830)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 1 (meaning819 q) (meaning830 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 830 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 826 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (826)) (literal (valuationOf q) (831)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 1 1 (meaning819 q) (meaning826 q) (meaning831 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 826 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 826 = false ∨ valuation q 831 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 827 = false ∨ valuationOf q 832 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (827)) (literal (valuationOf q) (832)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 1 2 (meaning819 q) (meaning827 q) (meaning832 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 827 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 827 = false ∨ valuation q 832 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 828 = false ∨ valuationOf q 833 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (828)) (literal (valuationOf q) (833)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 1 3 (meaning819 q) (meaning828 q) (meaning833 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 828 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 828 = false ∨ valuation q 833 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 819 = false ∨ valuationOf q 829 = false ∨ valuationOf q 834 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (819)) (literal (valuationOf q) (829)) (literal (valuationOf q) (834)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 1 4 (meaning819 q) (meaning829 q) (meaning834 q) hs
  change valuationOf q 819 = false ∨ valuationOf q 829 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 819 = false ∨ valuation q 829 = false ∨ valuation q 834 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 831 = true := by
  have hs : count830 q = (countLit q [-16, -18, -19]) + (countLit q [-21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-16, -18, -19]) (l₂ := [-21, -22, -24, -25])
  have hm := merge_left (literal (valuationOf q) (820)) (literal (valuationOf q) (831)) (countLit q [-16, -18, -19]) (countLit q [-21, -22, -24, -25]) (count830 q) 2 (meaning820 q) (meaning831 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 831 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E115.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112115
