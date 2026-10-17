import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 832 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_left (literal (valuationOf q) (805)) (literal (valuationOf q) (832)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 6 (meaning805 q) (meaning832 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 832 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 832 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 820 = false ∨ valuationOf q 833 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (820)) (literal (valuationOf q) (833)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 6 1 (meaning805 q) (meaning820 q) (meaning833 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 820 = false ∨ valuationOf q 833 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 820 = false ∨ valuation q 833 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 821 = false ∨ valuationOf q 834 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (821)) (literal (valuationOf q) (834)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 6 2 (meaning805 q) (meaning821 q) (meaning834 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 821 = false ∨ valuationOf q 834 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 821 = false ∨ valuation q 834 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 822 = false ∨ valuationOf q 835 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (822)) (literal (valuationOf q) (835)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 6 3 (meaning805 q) (meaning822 q) (meaning835 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 822 = false ∨ valuationOf q 835 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 822 = false ∨ valuation q 835 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 805 = false ∨ valuationOf q 823 = false ∨ valuationOf q 836 = true := by
  have hs : count827 q = (countLit q [-1, -2, -6, -7, -10, -11, -14]) + (countLit q [-15, -17, -19, -21, -23, -25, -27]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -6, -7, -10, -11, -14]) (l₂ := [-15, -17, -19, -21, -23, -25, -27])
  have hm := merge_two (literal (valuationOf q) (805)) (literal (valuationOf q) (823)) (literal (valuationOf q) (836)) (countLit q [-1, -2, -6, -7, -10, -11, -14]) (countLit q [-15, -17, -19, -21, -23, -25, -27]) (count827 q) 6 4 (meaning805 q) (meaning823 q) (meaning836 q) hs
  change valuationOf q 805 = false ∨ valuationOf q 823 = false ∨ valuationOf q 836 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 805 = false ∨ valuation q 823 = false ∨ valuation q 836 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 841 = true := by
  have hs : count841 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (841)) (countLit q [-32]) (countLit q [-34]) (count841 q) 1 (meaningNeg34 q) (meaning841 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 841 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 841 = true := by
  have hs : count841 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (841)) (countLit q [-32]) (countLit q [-34]) (count841 q) 1 (meaningNeg32 q) (meaning841 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 841 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 34 = true ∨ valuationOf q 842 = true := by
  have hs : count841 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (842)) (countLit q [-32]) (countLit q [-34]) (count841 q) 1 1 (meaningNeg32 q) (meaningNeg34 q) (meaning842 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 842 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 843 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_right (literal (valuationOf q) (841)) (literal (valuationOf q) (843)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 1 (meaning841 q) (meaning843 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 843 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 842 = false ∨ valuationOf q 844 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_right (literal (valuationOf q) (842)) (literal (valuationOf q) (844)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 2 (meaning842 q) (meaning844 q) hs
  change valuationOf q 842 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 842 = false ∨ valuation q 844 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 843 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (843)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 1 (meaningNeg30 q) (meaning843 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 843 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 841 = false ∨ valuationOf q 844 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (841)) (literal (valuationOf q) (844)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 1 1 (meaningNeg30 q) (meaning841 q) (meaning844 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 841 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 841 = false ∨ valuation q 844 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 842 = false ∨ valuationOf q 845 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (842)) (literal (valuationOf q) (845)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 1 2 (meaningNeg30 q) (meaning842 q) (meaning845 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 842 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 842 = false ∨ valuation q 845 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 38 = true ∨ valuationOf q 846 = true := by
  have hs : count846 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_right (literal (valuationOf q) (-38)) (literal (valuationOf q) (846)) (countLit q [-36]) (countLit q [-38]) (count846 q) 1 (meaningNeg38 q) (meaning846 q) hs
  change (! (valuationOf q 38)) = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 38 = true ∨ valuation q 846 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 846 = true := by
  have hs : count846 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_left (literal (valuationOf q) (-36)) (literal (valuationOf q) (846)) (countLit q [-36]) (countLit q [-38]) (count846 q) 1 (meaningNeg36 q) (meaning846 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 846 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 38 = true ∨ valuationOf q 847 = true := by
  have hs : count846 q = (countLit q [-36]) + (countLit q [-38]) := List.countP_append (p := literal q) (l₁ := [-36]) (l₂ := [-38])
  have hm := merge_two (literal (valuationOf q) (-36)) (literal (valuationOf q) (-38)) (literal (valuationOf q) (847)) (countLit q [-36]) (countLit q [-38]) (count846 q) 1 1 (meaningNeg36 q) (meaningNeg38 q) (meaning847 q) hs
  change (! (valuationOf q 36)) = false ∨ (! (valuationOf q 38)) = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 38 = true ∨ valuation q 847 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 848 = true := by
  have hs : count848 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (848)) (countLit q [-39]) (countLit q [-42]) (count848 q) 1 (meaningNeg42 q) (meaning848 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 848 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 848 = true := by
  have hs : count848 q = (countLit q [-39]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (848)) (countLit q [-39]) (countLit q [-42]) (count848 q) 1 (meaningNeg39 q) (meaning848 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 848 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 850 = true := by
  have hs : count850 q = (countLit q [-36, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-39, -42])
  have hm := merge_right (literal (valuationOf q) (848)) (literal (valuationOf q) (850)) (countLit q [-36, -38]) (countLit q [-39, -42]) (count850 q) 1 (meaning848 q) (meaning850 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 850 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 850 = true := by
  have hs : count850 q = (countLit q [-36, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-39, -42])
  have hm := merge_left (literal (valuationOf q) (846)) (literal (valuationOf q) (850)) (countLit q [-36, -38]) (countLit q [-39, -42]) (count850 q) 1 (meaning846 q) (meaning850 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 850 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 848 = false ∨ valuationOf q 851 = true := by
  have hs : count850 q = (countLit q [-36, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (848)) (literal (valuationOf q) (851)) (countLit q [-36, -38]) (countLit q [-39, -42]) (count850 q) 1 1 (meaning846 q) (meaning848 q) (meaning851 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 848 = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 848 = false ∨ valuation q 851 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 848 = false ∨ valuationOf q 852 = true := by
  have hs : count850 q = (countLit q [-36, -38]) + (countLit q [-39, -42]) := List.countP_append (p := literal q) (l₁ := [-36, -38]) (l₂ := [-39, -42])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (848)) (literal (valuationOf q) (852)) (countLit q [-36, -38]) (countLit q [-39, -42]) (count850 q) 2 1 (meaning847 q) (meaning848 q) (meaning852 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 848 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 848 = false ∨ valuation q 852 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 854 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_right (literal (valuationOf q) (850)) (literal (valuationOf q) (854)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 1 (meaning850 q) (meaning854 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 854 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_right (literal (valuationOf q) (851)) (literal (valuationOf q) (855)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 2 (meaning851 q) (meaning855 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 855 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 854 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_left (literal (valuationOf q) (843)) (literal (valuationOf q) (854)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 1 (meaning843 q) (meaning854 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 854 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 850 = false ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (850)) (literal (valuationOf q) (855)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 1 1 (meaning843 q) (meaning850 q) (meaning855 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 850 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 850 = false ∨ valuation q 855 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 851 = false ∨ valuationOf q 856 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (851)) (literal (valuationOf q) (856)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 1 2 (meaning843 q) (meaning851 q) (meaning856 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 851 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 851 = false ∨ valuation q 856 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 852 = false ∨ valuationOf q 857 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (852)) (literal (valuationOf q) (857)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 1 3 (meaning843 q) (meaning852 q) (meaning857 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 852 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 852 = false ∨ valuation q 857 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_left (literal (valuationOf q) (844)) (literal (valuationOf q) (855)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 2 (meaning844 q) (meaning855 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 855 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 850 = false ∨ valuationOf q 856 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (850)) (literal (valuationOf q) (856)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 2 1 (meaning844 q) (meaning850 q) (meaning856 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 850 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 850 = false ∨ valuation q 856 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 851 = false ∨ valuationOf q 857 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (851)) (literal (valuationOf q) (857)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 2 2 (meaning844 q) (meaning851 q) (meaning857 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 851 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 851 = false ∨ valuation q 857 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 856 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_left (literal (valuationOf q) (845)) (literal (valuationOf q) (856)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 3 (meaning845 q) (meaning856 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 856 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E259.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112259
