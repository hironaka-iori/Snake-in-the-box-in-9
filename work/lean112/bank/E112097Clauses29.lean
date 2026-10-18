import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 8 = true ∨ valuationOf q 10 = true ∨ valuationOf q 841 = true := by
  have hs : count840 q = (countLit q [-8]) + (countLit q [-10]) := List.countP_append (p := literal q) (l₁ := [-8]) (l₂ := [-10])
  have hm := merge_two (literal (valuationOf q) (-8)) (literal (valuationOf q) (-10)) (literal (valuationOf q) (841)) (countLit q [-8]) (countLit q [-10]) (count840 q) 1 1 (meaningNeg8 q) (meaningNeg10 q) (meaning841 q) hs
  change (! (valuationOf q 8)) = false ∨ (! (valuationOf q 10)) = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 8 = true ∨ valuation q 10 = true ∨ valuation q 841 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 840 = false ∨ valuationOf q 842 = true := by
  have hs : count842 q = (countLit q [-6, -7]) + (countLit q [-8, -10]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -10])
  have hm := merge_right (literal (valuationOf q) (840)) (literal (valuationOf q) (842)) (countLit q [-6, -7]) (countLit q [-8, -10]) (count842 q) 1 (meaning840 q) (meaning842 q) hs
  change valuationOf q 840 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 840 = false ∨ valuation q 842 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 841 = false ∨ valuationOf q 843 = true := by
  have hs : count842 q = (countLit q [-6, -7]) + (countLit q [-8, -10]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -10])
  have hm := merge_right (literal (valuationOf q) (841)) (literal (valuationOf q) (843)) (countLit q [-6, -7]) (countLit q [-8, -10]) (count842 q) 2 (meaning841 q) (meaning843 q) hs
  change valuationOf q 841 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 841 = false ∨ valuation q 843 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 842 = true := by
  have hs : count842 q = (countLit q [-6, -7]) + (countLit q [-8, -10]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -10])
  have hm := merge_left (literal (valuationOf q) (838)) (literal (valuationOf q) (842)) (countLit q [-6, -7]) (countLit q [-8, -10]) (count842 q) 1 (meaning838 q) (meaning842 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 842 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 840 = false ∨ valuationOf q 843 = true := by
  have hs : count842 q = (countLit q [-6, -7]) + (countLit q [-8, -10]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -10])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (840)) (literal (valuationOf q) (843)) (countLit q [-6, -7]) (countLit q [-8, -10]) (count842 q) 1 1 (meaning838 q) (meaning840 q) (meaning843 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 840 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 840 = false ∨ valuation q 843 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 838 = false ∨ valuationOf q 841 = false ∨ valuationOf q 844 = true := by
  have hs : count842 q = (countLit q [-6, -7]) + (countLit q [-8, -10]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -10])
  have hm := merge_two (literal (valuationOf q) (838)) (literal (valuationOf q) (841)) (literal (valuationOf q) (844)) (countLit q [-6, -7]) (countLit q [-8, -10]) (count842 q) 1 2 (meaning838 q) (meaning841 q) (meaning844 q) hs
  change valuationOf q 838 = false ∨ valuationOf q 841 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 838 = false ∨ valuation q 841 = false ∨ valuation q 844 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 843 = true := by
  have hs : count842 q = (countLit q [-6, -7]) + (countLit q [-8, -10]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -10])
  have hm := merge_left (literal (valuationOf q) (839)) (literal (valuationOf q) (843)) (countLit q [-6, -7]) (countLit q [-8, -10]) (count842 q) 2 (meaning839 q) (meaning843 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 843 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 839 = false ∨ valuationOf q 840 = false ∨ valuationOf q 844 = true := by
  have hs : count842 q = (countLit q [-6, -7]) + (countLit q [-8, -10]) := List.countP_append (p := literal q) (l₁ := [-6, -7]) (l₂ := [-8, -10])
  have hm := merge_two (literal (valuationOf q) (839)) (literal (valuationOf q) (840)) (literal (valuationOf q) (844)) (countLit q [-6, -7]) (countLit q [-8, -10]) (count842 q) 2 1 (meaning839 q) (meaning840 q) (meaning844 q) hs
  change valuationOf q 839 = false ∨ valuationOf q 840 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 839 = false ∨ valuation q 840 = false ∨ valuation q 844 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 836 = false ∨ valuationOf q 843 = false ∨ valuationOf q 849 = true := by
  have hs : count846 q = (countLit q [-1, -3, -4]) + (countLit q [-6, -7, -8, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-6, -7, -8, -10])
  have hm := merge_two (literal (valuationOf q) (836)) (literal (valuationOf q) (843)) (literal (valuationOf q) (849)) (countLit q [-1, -3, -4]) (countLit q [-6, -7, -8, -10]) (count846 q) 2 2 (meaning836 q) (meaning843 q) (meaning849 q) hs
  change valuationOf q 836 = false ∨ valuationOf q 843 = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 836 = false ∨ valuation q 843 = false ∨ valuation q 849 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 848 = true := by
  have hs : count846 q = (countLit q [-1, -3, -4]) + (countLit q [-6, -7, -8, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-6, -7, -8, -10])
  have hm := merge_left (literal (valuationOf q) (837)) (literal (valuationOf q) (848)) (countLit q [-1, -3, -4]) (countLit q [-6, -7, -8, -10]) (count846 q) 3 (meaning837 q) (meaning848 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 848 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 842 = false ∨ valuationOf q 849 = true := by
  have hs : count846 q = (countLit q [-1, -3, -4]) + (countLit q [-6, -7, -8, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-6, -7, -8, -10])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (842)) (literal (valuationOf q) (849)) (countLit q [-1, -3, -4]) (countLit q [-6, -7, -8, -10]) (count846 q) 3 1 (meaning837 q) (meaning842 q) (meaning849 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 842 = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 842 = false ∨ valuation q 849 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 843 = false ∨ valuationOf q 850 = true := by
  have hs : count846 q = (countLit q [-1, -3, -4]) + (countLit q [-6, -7, -8, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-6, -7, -8, -10])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (843)) (literal (valuationOf q) (850)) (countLit q [-1, -3, -4]) (countLit q [-6, -7, -8, -10]) (count846 q) 3 2 (meaning837 q) (meaning843 q) (meaning850 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 843 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 843 = false ∨ valuation q 850 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 837 = false ∨ valuationOf q 844 = false ∨ valuationOf q 851 = true := by
  have hs : count846 q = (countLit q [-1, -3, -4]) + (countLit q [-6, -7, -8, -10]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4]) (l₂ := [-6, -7, -8, -10])
  have hm := merge_two (literal (valuationOf q) (837)) (literal (valuationOf q) (844)) (literal (valuationOf q) (851)) (countLit q [-1, -3, -4]) (countLit q [-6, -7, -8, -10]) (count846 q) 3 3 (meaning837 q) (meaning844 q) (meaning851 q) hs
  change valuationOf q 837 = false ∨ valuationOf q 844 = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 837 = false ∨ valuation q 844 = false ∨ valuation q 851 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 853 = true := by
  have hs : count853 q = (countLit q [-13]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (853)) (countLit q [-13]) (countLit q [-18]) (count853 q) 1 (meaningNeg18 q) (meaning853 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 853 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 853 = true := by
  have hs : count853 q = (countLit q [-13]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (853)) (countLit q [-13]) (countLit q [-18]) (count853 q) 1 (meaningNeg13 q) (meaning853 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 853 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 18 = true ∨ valuationOf q 854 = true := by
  have hs : count853 q = (countLit q [-13]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (854)) (countLit q [-13]) (countLit q [-18]) (count853 q) 1 1 (meaningNeg13 q) (meaningNeg18 q) (meaning854 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 18 = true ∨ valuation q 854 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 855 = true := by
  have hs : count855 q = (countLit q [-20]) + (countLit q [-21]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-21])
  have hm := merge_right (literal (valuationOf q) (-21)) (literal (valuationOf q) (855)) (countLit q [-20]) (countLit q [-21]) (count855 q) 1 (meaningNeg21 q) (meaning855 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 855 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 857 = true := by
  have hs : count857 q = (countLit q [-13, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-13, -18]) (l₂ := [-20, -21])
  have hm := merge_right (literal (valuationOf q) (855)) (literal (valuationOf q) (857)) (countLit q [-13, -18]) (countLit q [-20, -21]) (count857 q) 1 (meaning855 q) (meaning857 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 857 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 857 = true := by
  have hs : count857 q = (countLit q [-13, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-13, -18]) (l₂ := [-20, -21])
  have hm := merge_left (literal (valuationOf q) (853)) (literal (valuationOf q) (857)) (countLit q [-13, -18]) (countLit q [-20, -21]) (count857 q) 1 (meaning853 q) (meaning857 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 857 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 855 = false ∨ valuationOf q 858 = true := by
  have hs : count857 q = (countLit q [-13, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-13, -18]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (855)) (literal (valuationOf q) (858)) (countLit q [-13, -18]) (countLit q [-20, -21]) (count857 q) 1 1 (meaning853 q) (meaning855 q) (meaning858 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 855 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 855 = false ∨ valuation q 858 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 858 = true := by
  have hs : count857 q = (countLit q [-13, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-13, -18]) (l₂ := [-20, -21])
  have hm := merge_left (literal (valuationOf q) (854)) (literal (valuationOf q) (858)) (countLit q [-13, -18]) (countLit q [-20, -21]) (count857 q) 2 (meaning854 q) (meaning858 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 858 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 855 = false ∨ valuationOf q 859 = true := by
  have hs : count857 q = (countLit q [-13, -18]) + (countLit q [-20, -21]) := List.countP_append (p := literal q) (l₁ := [-13, -18]) (l₂ := [-20, -21])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (855)) (literal (valuationOf q) (859)) (countLit q [-13, -18]) (countLit q [-20, -21]) (count857 q) 2 1 (meaning854 q) (meaning855 q) (meaning859 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 855 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 855 = false ∨ valuation q 859 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 25 = true ∨ valuationOf q 861 = true := by
  have hs : count861 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_right (literal (valuationOf q) (-25)) (literal (valuationOf q) (861)) (countLit q [-22]) (countLit q [-25]) (count861 q) 1 (meaningNeg25 q) (meaning861 q) hs
  change (! (valuationOf q 25)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 25 = true ∨ valuation q 861 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 861 = true := by
  have hs : count861 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_left (literal (valuationOf q) (-22)) (literal (valuationOf q) (861)) (countLit q [-22]) (countLit q [-25]) (count861 q) 1 (meaningNeg22 q) (meaning861 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 861 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 25 = true ∨ valuationOf q 862 = true := by
  have hs : count861 q = (countLit q [-22]) + (countLit q [-25]) := List.countP_append (p := literal q) (l₁ := [-22]) (l₂ := [-25])
  have hm := merge_two (literal (valuationOf q) (-22)) (literal (valuationOf q) (-25)) (literal (valuationOf q) (862)) (countLit q [-22]) (countLit q [-25]) (count861 q) 1 1 (meaningNeg22 q) (meaningNeg25 q) (meaning862 q) hs
  change (! (valuationOf q 22)) = false ∨ (! (valuationOf q 25)) = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 25 = true ∨ valuation q 862 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (863)) (countLit q [-28]) (countLit q [-29]) (count863 q) 1 (meaningNeg29 q) (meaning863 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 863 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (863)) (countLit q [-28]) (countLit q [-29]) (count863 q) 1 (meaningNeg28 q) (meaning863 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 863 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 29 = true ∨ valuationOf q 864 = true := by
  have hs : count863 q = (countLit q [-28]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (864)) (countLit q [-28]) (countLit q [-29]) (count863 q) 1 1 (meaningNeg28 q) (meaningNeg29 q) (meaning864 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 29 = true ∨ valuation q 864 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-22, -25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-28, -29])
  have hm := merge_right (literal (valuationOf q) (863)) (literal (valuationOf q) (865)) (countLit q [-22, -25]) (countLit q [-28, -29]) (count865 q) 1 (meaning863 q) (meaning865 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 865 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-22, -25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-28, -29])
  have hm := merge_right (literal (valuationOf q) (864)) (literal (valuationOf q) (866)) (countLit q [-22, -25]) (countLit q [-28, -29]) (count865 q) 2 (meaning864 q) (meaning866 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 866 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-22, -25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-28, -29])
  have hm := merge_left (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-22, -25]) (countLit q [-28, -29]) (count865 q) 1 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-22, -25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-28, -29])
  have hm := merge_two (literal (valuationOf q) (861)) (literal (valuationOf q) (863)) (literal (valuationOf q) (866)) (countLit q [-22, -25]) (countLit q [-28, -29]) (count865 q) 1 1 (meaning861 q) (meaning863 q) (meaning866 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 863 = false ∨ valuation q 866 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E097.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112097
