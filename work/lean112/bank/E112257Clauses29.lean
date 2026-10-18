import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause929 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 843 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (843)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 1 (meaningNeg30 q) (meaning843 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 843 = true := counterClause929 (baseVal q)

theorem counterClause930 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 841 = false ∨ valuationOf q 844 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (841)) (literal (valuationOf q) (844)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 1 1 (meaningNeg30 q) (meaning841 q) (meaning844 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 841 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 841 = false ∨ valuation q 844 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 842 = false ∨ valuationOf q 845 = true := by
  have hs : count843 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (842)) (literal (valuationOf q) (845)) (countLit q [-30]) (countLit q [-32, -34]) (count843 q) 1 2 (meaningNeg30 q) (meaning842 q) (meaning845 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 842 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 842 = false ∨ valuation q 845 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 846 = true := by
  have hs : count846 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_right (literal (valuationOf q) (-42)) (literal (valuationOf q) (846)) (countLit q [-40]) (countLit q [-42]) (count846 q) 1 (meaningNeg42 q) (meaning846 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 846 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 846 = true := by
  have hs : count846 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_left (literal (valuationOf q) (-40)) (literal (valuationOf q) (846)) (countLit q [-40]) (countLit q [-42]) (count846 q) 1 (meaningNeg40 q) (meaning846 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 846 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 846 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 42 = true ∨ valuationOf q 847 = true := by
  have hs : count846 q = (countLit q [-40]) + (countLit q [-42]) := List.countP_append (p := literal q) (l₁ := [-40]) (l₂ := [-42])
  have hm := merge_two (literal (valuationOf q) (-40)) (literal (valuationOf q) (-42)) (literal (valuationOf q) (847)) (countLit q [-40]) (countLit q [-42]) (count846 q) 1 1 (meaningNeg40 q) (meaningNeg42 q) (meaning847 q) hs
  change (! (valuationOf q 40)) = false ∨ (! (valuationOf q 42)) = false ∨ valuationOf q 847 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 42 = true ∨ valuation q 847 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 45 = true ∨ valuationOf q 848 = true := by
  have hs : count848 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_right (literal (valuationOf q) (-45)) (literal (valuationOf q) (848)) (countLit q [-44]) (countLit q [-45]) (count848 q) 1 (meaningNeg45 q) (meaning848 q) hs
  change (! (valuationOf q 45)) = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 45 = true ∨ valuation q 848 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 848 = true := by
  have hs : count848 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (848)) (countLit q [-44]) (countLit q [-45]) (count848 q) 1 (meaningNeg44 q) (meaning848 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 848 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 848 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 45 = true ∨ valuationOf q 849 = true := by
  have hs : count848 q = (countLit q [-44]) + (countLit q [-45]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-45])
  have hm := merge_two (literal (valuationOf q) (-44)) (literal (valuationOf q) (-45)) (literal (valuationOf q) (849)) (countLit q [-44]) (countLit q [-45]) (count848 q) 1 1 (meaningNeg44 q) (meaningNeg45 q) (meaning849 q) hs
  change (! (valuationOf q 44)) = false ∨ (! (valuationOf q 45)) = false ∨ valuationOf q 849 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 45 = true ∨ valuation q 849 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 850 = true := by
  have hs : count850 q = (countLit q [-40, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -45])
  have hm := merge_right (literal (valuationOf q) (848)) (literal (valuationOf q) (850)) (countLit q [-40, -42]) (countLit q [-44, -45]) (count850 q) 1 (meaning848 q) (meaning850 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 850 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 851 = true := by
  have hs : count850 q = (countLit q [-40, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -45])
  have hm := merge_right (literal (valuationOf q) (849)) (literal (valuationOf q) (851)) (countLit q [-40, -42]) (countLit q [-44, -45]) (count850 q) 2 (meaning849 q) (meaning851 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 851 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 850 = true := by
  have hs : count850 q = (countLit q [-40, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -45])
  have hm := merge_left (literal (valuationOf q) (846)) (literal (valuationOf q) (850)) (countLit q [-40, -42]) (countLit q [-44, -45]) (count850 q) 1 (meaning846 q) (meaning850 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 850 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 850 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 848 = false ∨ valuationOf q 851 = true := by
  have hs : count850 q = (countLit q [-40, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (848)) (literal (valuationOf q) (851)) (countLit q [-40, -42]) (countLit q [-44, -45]) (count850 q) 1 1 (meaning846 q) (meaning848 q) (meaning851 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 848 = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 848 = false ∨ valuation q 851 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 846 = false ∨ valuationOf q 849 = false ∨ valuationOf q 852 = true := by
  have hs : count850 q = (countLit q [-40, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (846)) (literal (valuationOf q) (849)) (literal (valuationOf q) (852)) (countLit q [-40, -42]) (countLit q [-44, -45]) (count850 q) 1 2 (meaning846 q) (meaning849 q) (meaning852 q) hs
  change valuationOf q 846 = false ∨ valuationOf q 849 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 846 = false ∨ valuation q 849 = false ∨ valuation q 852 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 851 = true := by
  have hs : count850 q = (countLit q [-40, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -45])
  have hm := merge_left (literal (valuationOf q) (847)) (literal (valuationOf q) (851)) (countLit q [-40, -42]) (countLit q [-44, -45]) (count850 q) 2 (meaning847 q) (meaning851 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 851 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 848 = false ∨ valuationOf q 852 = true := by
  have hs : count850 q = (countLit q [-40, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (848)) (literal (valuationOf q) (852)) (countLit q [-40, -42]) (countLit q [-44, -45]) (count850 q) 2 1 (meaning847 q) (meaning848 q) (meaning852 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 848 = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 848 = false ∨ valuation q 852 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 847 = false ∨ valuationOf q 849 = false ∨ valuationOf q 853 = true := by
  have hs : count850 q = (countLit q [-40, -42]) + (countLit q [-44, -45]) := List.countP_append (p := literal q) (l₁ := [-40, -42]) (l₂ := [-44, -45])
  have hm := merge_two (literal (valuationOf q) (847)) (literal (valuationOf q) (849)) (literal (valuationOf q) (853)) (countLit q [-40, -42]) (countLit q [-44, -45]) (count850 q) 2 2 (meaning847 q) (meaning849 q) (meaning853 q) hs
  change valuationOf q 847 = false ∨ valuationOf q 849 = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 847 = false ∨ valuation q 849 = false ∨ valuation q 853 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 854 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_right (literal (valuationOf q) (850)) (literal (valuationOf q) (854)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 1 (meaning850 q) (meaning854 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 854 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_right (literal (valuationOf q) (851)) (literal (valuationOf q) (855)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 2 (meaning851 q) (meaning855 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 855 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 856 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_right (literal (valuationOf q) (852)) (literal (valuationOf q) (856)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 3 (meaning852 q) (meaning856 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 856 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 857 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_right (literal (valuationOf q) (853)) (literal (valuationOf q) (857)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 4 (meaning853 q) (meaning857 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 857 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 854 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_left (literal (valuationOf q) (843)) (literal (valuationOf q) (854)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 1 (meaning843 q) (meaning854 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 854 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 850 = false ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (850)) (literal (valuationOf q) (855)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 1 1 (meaning843 q) (meaning850 q) (meaning855 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 850 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 850 = false ∨ valuation q 855 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 851 = false ∨ valuationOf q 856 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (851)) (literal (valuationOf q) (856)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 1 2 (meaning843 q) (meaning851 q) (meaning856 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 851 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 851 = false ∨ valuation q 856 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 852 = false ∨ valuationOf q 857 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (852)) (literal (valuationOf q) (857)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 1 3 (meaning843 q) (meaning852 q) (meaning857 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 852 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 852 = false ∨ valuation q 857 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 843 = false ∨ valuationOf q 853 = false ∨ valuationOf q 858 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (843)) (literal (valuationOf q) (853)) (literal (valuationOf q) (858)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 1 4 (meaning843 q) (meaning853 q) (meaning858 q) hs
  change valuationOf q 843 = false ∨ valuationOf q 853 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 843 = false ∨ valuation q 853 = false ∨ valuation q 858 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 855 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_left (literal (valuationOf q) (844)) (literal (valuationOf q) (855)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 2 (meaning844 q) (meaning855 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 855 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 850 = false ∨ valuationOf q 856 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (850)) (literal (valuationOf q) (856)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 2 1 (meaning844 q) (meaning850 q) (meaning856 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 850 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 850 = false ∨ valuation q 856 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 851 = false ∨ valuationOf q 857 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (851)) (literal (valuationOf q) (857)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 2 2 (meaning844 q) (meaning851 q) (meaning857 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 851 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 851 = false ∨ valuation q 857 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 852 = false ∨ valuationOf q 858 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (852)) (literal (valuationOf q) (858)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 2 3 (meaning844 q) (meaning852 q) (meaning858 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 852 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 852 = false ∨ valuation q 858 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 844 = false ∨ valuationOf q 853 = false ∨ valuationOf q 859 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (844)) (literal (valuationOf q) (853)) (literal (valuationOf q) (859)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 2 4 (meaning844 q) (meaning853 q) (meaning859 q) hs
  change valuationOf q 844 = false ∨ valuationOf q 853 = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 844 = false ∨ valuation q 853 = false ∨ valuation q 859 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 856 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_left (literal (valuationOf q) (845)) (literal (valuationOf q) (856)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 3 (meaning845 q) (meaning856 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 856 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E257.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112257
