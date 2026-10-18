import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 811 = false ∨ valuationOf q 835 = false ∨ valuationOf q 844 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (811)) (literal (valuationOf q) (835)) (literal (valuationOf q) (844)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 2 6 (meaning811 q) (meaning835 q) (meaning844 q) hs
  change valuationOf q 811 = false ∨ valuationOf q 835 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 811 = false ∨ valuation q 835 = false ∨ valuation q 844 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 831 = false ∨ valuationOf q 841 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (831)) (literal (valuationOf q) (841)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 3 2 (meaning812 q) (meaning831 q) (meaning841 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 831 = false ∨ valuationOf q 841 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 831 = false ∨ valuation q 841 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 832 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (832)) (literal (valuationOf q) (842)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 3 3 (meaning812 q) (meaning832 q) (meaning842 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 832 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 832 = false ∨ valuation q 842 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 833 = false ∨ valuationOf q 843 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (833)) (literal (valuationOf q) (843)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 3 4 (meaning812 q) (meaning833 q) (meaning843 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 833 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 833 = false ∨ valuation q 843 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 834 = false ∨ valuationOf q 844 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (834)) (literal (valuationOf q) (844)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 3 5 (meaning812 q) (meaning834 q) (meaning844 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 834 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 834 = false ∨ valuation q 844 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 812 = false ∨ valuationOf q 835 = false ∨ valuationOf q 845 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (812)) (literal (valuationOf q) (835)) (literal (valuationOf q) (845)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 3 6 (meaning812 q) (meaning835 q) (meaning845 q) hs
  change valuationOf q 812 = false ∨ valuationOf q 835 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 812 = false ∨ valuation q 835 = false ∨ valuation q 845 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 831 = false ∨ valuationOf q 842 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (831)) (literal (valuationOf q) (842)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 4 2 (meaning813 q) (meaning831 q) (meaning842 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 831 = false ∨ valuationOf q 842 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 831 = false ∨ valuation q 842 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 832 = false ∨ valuationOf q 843 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (832)) (literal (valuationOf q) (843)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 4 3 (meaning813 q) (meaning832 q) (meaning843 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 832 = false ∨ valuationOf q 843 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 832 = false ∨ valuation q 843 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 833 = false ∨ valuationOf q 844 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (833)) (literal (valuationOf q) (844)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 4 4 (meaning813 q) (meaning833 q) (meaning844 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 833 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 833 = false ∨ valuation q 844 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 813 = false ∨ valuationOf q 834 = false ∨ valuationOf q 845 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (813)) (literal (valuationOf q) (834)) (literal (valuationOf q) (845)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 4 5 (meaning813 q) (meaning834 q) (meaning845 q) hs
  change valuationOf q 813 = false ∨ valuationOf q 834 = false ∨ valuationOf q 845 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 813 = false ∨ valuation q 834 = false ∨ valuation q 845 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 814 = false ∨ valuationOf q 832 = false ∨ valuationOf q 844 = true := by
  have hs : count837 q = (countLit q [-1, -3, -6, -8, -11, -13, -14]) + (countLit q [-16, -17, -20, -21, -22, -24, -25]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -6, -8, -11, -13, -14]) (l₂ := [-16, -17, -20, -21, -22, -24, -25])
  have hm := merge_two (literal (valuationOf q) (814)) (literal (valuationOf q) (832)) (literal (valuationOf q) (844)) (countLit q [-1, -3, -6, -8, -11, -13, -14]) (countLit q [-16, -17, -20, -21, -22, -24, -25]) (count837 q) 5 3 (meaning814 q) (meaning832 q) (meaning844 q) hs
  change valuationOf q 814 = false ∨ valuationOf q 832 = false ∨ valuationOf q 844 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 814 = false ∨ valuation q 832 = false ∨ valuation q 844 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 33 = true ∨ valuationOf q 851 = true := by
  have hs : count851 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_right (literal (valuationOf q) (-33)) (literal (valuationOf q) (851)) (countLit q [-30]) (countLit q [-33]) (count851 q) 1 (meaningNeg33 q) (meaning851 q) hs
  change (! (valuationOf q 33)) = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 33 = true ∨ valuation q 851 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 851 = true := by
  have hs : count851 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_left (literal (valuationOf q) (-30)) (literal (valuationOf q) (851)) (countLit q [-30]) (countLit q [-33]) (count851 q) 1 (meaningNeg30 q) (meaning851 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 851 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 851 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 33 = true ∨ valuationOf q 852 = true := by
  have hs : count851 q = (countLit q [-30]) + (countLit q [-33]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-33])
  have hm := merge_two (literal (valuationOf q) (-30)) (literal (valuationOf q) (-33)) (literal (valuationOf q) (852)) (countLit q [-30]) (countLit q [-33]) (count851 q) 1 1 (meaningNeg30 q) (meaningNeg33 q) (meaning852 q) hs
  change (! (valuationOf q 30)) = false ∨ (! (valuationOf q 33)) = false ∨ valuationOf q 852 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 33 = true ∨ valuation q 852 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 853 = true := by
  have hs : count853 q = (countLit q [-27]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -33])
  have hm := merge_right (literal (valuationOf q) (851)) (literal (valuationOf q) (853)) (countLit q [-27]) (countLit q [-30, -33]) (count853 q) 1 (meaning851 q) (meaning853 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 853 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 852 = false ∨ valuationOf q 854 = true := by
  have hs : count853 q = (countLit q [-27]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -33])
  have hm := merge_right (literal (valuationOf q) (852)) (literal (valuationOf q) (854)) (countLit q [-27]) (countLit q [-30, -33]) (count853 q) 2 (meaning852 q) (meaning854 q) hs
  change valuationOf q 852 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 852 = false ∨ valuation q 854 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 853 = true := by
  have hs : count853 q = (countLit q [-27]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -33])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (853)) (countLit q [-27]) (countLit q [-30, -33]) (count853 q) 1 (meaningNeg27 q) (meaning853 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 853 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 853 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true := by
  have hs : count853 q = (countLit q [-27]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -33])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (851)) (literal (valuationOf q) (854)) (countLit q [-27]) (countLit q [-30, -33]) (count853 q) 1 1 (meaningNeg27 q) (meaning851 q) (meaning854 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 851 = false ∨ valuationOf q 854 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 851 = false ∨ valuation q 854 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 852 = false ∨ valuationOf q 855 = true := by
  have hs : count853 q = (countLit q [-27]) + (countLit q [-30, -33]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30, -33])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (852)) (literal (valuationOf q) (855)) (countLit q [-27]) (countLit q [-30, -33]) (count853 q) 1 2 (meaningNeg27 q) (meaning852 q) (meaning855 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 852 = false ∨ valuationOf q 855 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 852 = false ∨ valuation q 855 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 37 = true ∨ valuationOf q 856 = true := by
  have hs : count856 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_right (literal (valuationOf q) (-37)) (literal (valuationOf q) (856)) (countLit q [-35]) (countLit q [-37]) (count856 q) 1 (meaningNeg37 q) (meaning856 q) hs
  change (! (valuationOf q 37)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 37 = true ∨ valuation q 856 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 856 = true := by
  have hs : count856 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_left (literal (valuationOf q) (-35)) (literal (valuationOf q) (856)) (countLit q [-35]) (countLit q [-37]) (count856 q) 1 (meaningNeg35 q) (meaning856 q) hs
  change (! (valuationOf q 35)) = false ∨ valuationOf q 856 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 856 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 35 = true ∨ valuationOf q 37 = true ∨ valuationOf q 857 = true := by
  have hs : count856 q = (countLit q [-35]) + (countLit q [-37]) := List.countP_append (p := literal q) (l₁ := [-35]) (l₂ := [-37])
  have hm := merge_two (literal (valuationOf q) (-35)) (literal (valuationOf q) (-37)) (literal (valuationOf q) (857)) (countLit q [-35]) (countLit q [-37]) (count856 q) 1 1 (meaningNeg35 q) (meaningNeg37 q) (meaning857 q) hs
  change (! (valuationOf q 35)) = false ∨ (! (valuationOf q 37)) = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 35 = true ∨ valuation q 37 = true ∨ valuation q 857 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 40 = true ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_right (literal (valuationOf q) (-40)) (literal (valuationOf q) (858)) (countLit q [-39]) (countLit q [-40]) (count858 q) 1 (meaningNeg40 q) (meaning858 q) hs
  change (! (valuationOf q 40)) = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 40 = true ∨ valuation q 858 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 858 = true := by
  have hs : count858 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_left (literal (valuationOf q) (-39)) (literal (valuationOf q) (858)) (countLit q [-39]) (countLit q [-40]) (count858 q) 1 (meaningNeg39 q) (meaning858 q) hs
  change (! (valuationOf q 39)) = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 858 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 39 = true ∨ valuationOf q 40 = true ∨ valuationOf q 859 = true := by
  have hs : count858 q = (countLit q [-39]) + (countLit q [-40]) := List.countP_append (p := literal q) (l₁ := [-39]) (l₂ := [-40])
  have hm := merge_two (literal (valuationOf q) (-39)) (literal (valuationOf q) (-40)) (literal (valuationOf q) (859)) (countLit q [-39]) (countLit q [-40]) (count858 q) 1 1 (meaningNeg39 q) (meaningNeg40 q) (meaning859 q) hs
  change (! (valuationOf q 39)) = false ∨ (! (valuationOf q 40)) = false ∨ valuationOf q 859 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 39 = true ∨ valuation q 40 = true ∨ valuation q 859 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-35, -37]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-39, -40])
  have hm := merge_right (literal (valuationOf q) (858)) (literal (valuationOf q) (860)) (countLit q [-35, -37]) (countLit q [-39, -40]) (count860 q) 1 (meaning858 q) (meaning860 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 860 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-35, -37]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-39, -40])
  have hm := merge_right (literal (valuationOf q) (859)) (literal (valuationOf q) (861)) (countLit q [-35, -37]) (countLit q [-39, -40]) (count860 q) 2 (meaning859 q) (meaning861 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 861 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 860 = true := by
  have hs : count860 q = (countLit q [-35, -37]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-39, -40])
  have hm := merge_left (literal (valuationOf q) (856)) (literal (valuationOf q) (860)) (countLit q [-35, -37]) (countLit q [-39, -40]) (count860 q) 1 (meaning856 q) (meaning860 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 860 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 860 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 858 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-35, -37]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (858)) (literal (valuationOf q) (861)) (countLit q [-35, -37]) (countLit q [-39, -40]) (count860 q) 1 1 (meaning856 q) (meaning858 q) (meaning861 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 858 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 858 = false ∨ valuation q 861 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 856 = false ∨ valuationOf q 859 = false ∨ valuationOf q 862 = true := by
  have hs : count860 q = (countLit q [-35, -37]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (856)) (literal (valuationOf q) (859)) (literal (valuationOf q) (862)) (countLit q [-35, -37]) (countLit q [-39, -40]) (count860 q) 1 2 (meaning856 q) (meaning859 q) (meaning862 q) hs
  change valuationOf q 856 = false ∨ valuationOf q 859 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 856 = false ∨ valuation q 859 = false ∨ valuation q 862 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-35, -37]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-39, -40])
  have hm := merge_left (literal (valuationOf q) (857)) (literal (valuationOf q) (861)) (countLit q [-35, -37]) (countLit q [-39, -40]) (count860 q) 2 (meaning857 q) (meaning861 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 861 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 858 = false ∨ valuationOf q 862 = true := by
  have hs : count860 q = (countLit q [-35, -37]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (858)) (literal (valuationOf q) (862)) (countLit q [-35, -37]) (countLit q [-39, -40]) (count860 q) 2 1 (meaning857 q) (meaning858 q) (meaning862 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 858 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 858 = false ∨ valuation q 862 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E213.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112213
