import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 815 = false ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-25, -27])
  have hm := merge_right (literal (valuationOf q) (815)) (literal (valuationOf q) (817)) (countLit q [-21, -23]) (countLit q [-25, -27]) (count816 q) 2 (meaning815 q) (meaning817 q) hs
  change valuationOf q 815 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 815 = false ∨ valuation q 817 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 816 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-25, -27])
  have hm := merge_left (literal (valuationOf q) (812)) (literal (valuationOf q) (816)) (countLit q [-21, -23]) (countLit q [-25, -27]) (count816 q) 1 (meaning812 q) (meaning816 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 816 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 816 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 814 = false ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (814)) (literal (valuationOf q) (817)) (countLit q [-21, -23]) (countLit q [-25, -27]) (count816 q) 1 1 (meaning812 q) (meaning814 q) (meaning817 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 814 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 814 = false ∨ valuation q 817 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 815 = false ∨ valuationOf q 818 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (815)) (literal (valuationOf q) (818)) (countLit q [-21, -23]) (countLit q [-25, -27]) (count816 q) 1 2 (meaning812 q) (meaning815 q) (meaning818 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 815 = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 815 = false ∨ valuation q 818 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 817 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-25, -27])
  have hm := merge_left (literal (valuationOf q) (813)) (literal (valuationOf q) (817)) (countLit q [-21, -23]) (countLit q [-25, -27]) (count816 q) 2 (meaning813 q) (meaning817 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 817 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 817 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 814 = false ∨ valuationOf q 818 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (814)) (literal (valuationOf q) (818)) (countLit q [-21, -23]) (countLit q [-25, -27]) (count816 q) 2 1 (meaning813 q) (meaning814 q) (meaning818 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 814 = false ∨ valuationOf q 818 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 814 = false ∨ valuation q 818 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 815 = false ∨ valuationOf q 819 = true := by
  have hs : count816 q = (countLit q [-21, -23]) + (countLit q [-25, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-25, -27])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (815)) (literal (valuationOf q) (819)) (countLit q [-21, -23]) (countLit q [-25, -27]) (count816 q) 2 2 (meaning813 q) (meaning815 q) (meaning819 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 815 = false ∨ valuationOf q 819 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 815 = false ∨ valuation q 819 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 816 = false ∨ valuationOf q 820 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (816)) (literal (valuationOf q) (820)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 1 (meaning816 q) (meaning820 q) hs
  change valuationOf q 816 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 816 = false ∨ valuation q 820 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 817 = false ∨ valuationOf q 821 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (817)) (literal (valuationOf q) (821)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 2 (meaning817 q) (meaning821 q) hs
  change valuationOf q 817 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 817 = false ∨ valuation q 821 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 818 = false ∨ valuationOf q 822 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (818)) (literal (valuationOf q) (822)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 3 (meaning818 q) (meaning822 q) hs
  change valuationOf q 818 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 818 = false ∨ valuation q 822 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 820 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (809)) (literal (valuationOf q) (820)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 1 (meaning809 q) (meaning820 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 820 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 820 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 816 = false ∨ valuationOf q 821 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (816)) (literal (valuationOf q) (821)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 1 1 (meaning809 q) (meaning816 q) (meaning821 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 816 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 816 = false ∨ valuation q 821 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 817 = false ∨ valuationOf q 822 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (817)) (literal (valuationOf q) (822)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 1 2 (meaning809 q) (meaning817 q) (meaning822 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 817 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 817 = false ∨ valuation q 822 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 818 = false ∨ valuationOf q 823 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (818)) (literal (valuationOf q) (823)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 1 3 (meaning809 q) (meaning818 q) (meaning823 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 818 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 818 = false ∨ valuation q 823 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 809 = false ∨ valuationOf q 819 = false ∨ valuationOf q 824 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (809)) (literal (valuationOf q) (819)) (literal (valuationOf q) (824)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 1 4 (meaning809 q) (meaning819 q) (meaning824 q) hs
  change valuationOf q 809 = false ∨ valuationOf q 819 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 809 = false ∨ valuation q 819 = false ∨ valuation q 824 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 821 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (810)) (literal (valuationOf q) (821)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 2 (meaning810 q) (meaning821 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 821 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 821 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 816 = false ∨ valuationOf q 822 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (816)) (literal (valuationOf q) (822)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 2 1 (meaning810 q) (meaning816 q) (meaning822 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 816 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 816 = false ∨ valuation q 822 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 817 = false ∨ valuationOf q 823 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (817)) (literal (valuationOf q) (823)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 2 2 (meaning810 q) (meaning817 q) (meaning823 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 817 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 817 = false ∨ valuation q 823 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 818 = false ∨ valuationOf q 824 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (818)) (literal (valuationOf q) (824)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 2 3 (meaning810 q) (meaning818 q) (meaning824 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 818 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 818 = false ∨ valuation q 824 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 810 = false ∨ valuationOf q 819 = false ∨ valuationOf q 825 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (810)) (literal (valuationOf q) (819)) (literal (valuationOf q) (825)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 2 4 (meaning810 q) (meaning819 q) (meaning825 q) hs
  change valuationOf q 810 = false ∨ valuationOf q 819 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 810 = false ∨ valuation q 819 = false ∨ valuation q 825 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 822 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (811)) (literal (valuationOf q) (822)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 3 (meaning811 q) (meaning822 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 822 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 822 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 816 = false ∨ valuationOf q 823 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (816)) (literal (valuationOf q) (823)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 3 1 (meaning811 q) (meaning816 q) (meaning823 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 816 = false ∨ valuationOf q 823 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 816 = false ∨ valuation q 823 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 817 = false ∨ valuationOf q 824 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (817)) (literal (valuationOf q) (824)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 3 2 (meaning811 q) (meaning817 q) (meaning824 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 817 = false ∨ valuationOf q 824 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 817 = false ∨ valuation q 824 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 818 = false ∨ valuationOf q 825 = true := by
  have hs : count820 q = (countLit q [-15, -17, -19]) + (countLit q [-21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -19]) (l₂ := [-21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (818)) (literal (valuationOf q) (825)) (countLit q [-15, -17, -19]) (countLit q [-21, -23, -25, -27]) (count820 q) 3 3 (meaning811 q) (meaning818 q) (meaning825 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 818 = false ∨ valuationOf q 825 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 818 = false ∨ valuation q 825 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 820 = false ∨ valuationOf q 827 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (820)) (literal (valuationOf q) (827)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 1 (meaning820 q) (meaning827 q) hs
  change valuationOf q 820 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 820 = false ∨ valuation q 827 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 821 = false ∨ valuationOf q 828 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (821)) (literal (valuationOf q) (828)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 2 (meaning821 q) (meaning828 q) hs
  change valuationOf q 821 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 821 = false ∨ valuation q 828 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 822 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (822)) (literal (valuationOf q) (829)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 3 (meaning822 q) (meaning829 q) hs
  change valuationOf q 822 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 822 = false ∨ valuation q 829 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 823 = false ∨ valuationOf q 830 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (823)) (literal (valuationOf q) (830)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 4 (meaning823 q) (meaning830 q) hs
  change valuationOf q 823 = false ∨ valuationOf q 830 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 823 = false ∨ valuation q 830 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 824 = false ∨ valuationOf q 831 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_right (literal (valuationOf q) (824)) (literal (valuationOf q) (831)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 5 (meaning824 q) (meaning831 q) hs
  change valuationOf q 824 = false ∨ valuationOf q 831 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 824 = false ∨ valuation q 831 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 827 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (800)) (literal (valuationOf q) (827)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 1 (meaning800 q) (meaning827 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 827 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 827 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 820 = false ∨ valuationOf q 828 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (820)) (literal (valuationOf q) (828)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 1 1 (meaning800 q) (meaning820 q) (meaning828 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 820 = false ∨ valuationOf q 828 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 820 = false ∨ valuation q 828 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 800 = false ∨ valuationOf q 821 = false ∨ valuationOf q 829 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (800)) (literal (valuationOf q) (821)) (literal (valuationOf q) (829)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 1 2 (meaning800 q) (meaning821 q) (meaning829 q) hs
  change valuationOf q 800 = false ∨ valuationOf q 821 = false ∨ valuationOf q 829 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 800 = false ∨ valuation q 821 = false ∨ valuation q 829 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E259.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112259
