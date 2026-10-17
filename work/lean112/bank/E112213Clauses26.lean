import E112213Semantics
import B112E213Inputs
namespace Snake9.Regrowth.E112213
noncomputable section
local instance blockDec26 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause833 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 859 = false ∨ valuationOf q 863 = true := by
  have hs : count860 q = (countLit q [-35, -37]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-35, -37]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (859)) (literal (valuationOf q) (863)) (countLit q [-35, -37]) (countLit q [-39, -40]) (count860 q) 2 2 (meaning857 q) (meaning859 q) (meaning863 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 859 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause833 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 859 = false ∨ valuation q 863 = true := counterClause833 (baseVal q)

theorem counterClause834 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_right (literal (valuationOf q) (860)) (literal (valuationOf q) (864)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 1 (meaning860 q) (meaning864 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause834 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 864 = true := counterClause834 (baseVal q)

theorem counterClause835 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_right (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 2 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause835 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause835 (baseVal q)

theorem counterClause836 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_right (literal (valuationOf q) (862)) (literal (valuationOf q) (866)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 3 (meaning862 q) (meaning866 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause836 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 866 = true := counterClause836 (baseVal q)

theorem counterClause837 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_right (literal (valuationOf q) (863)) (literal (valuationOf q) (867)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 4 (meaning863 q) (meaning867 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause837 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 867 = true := counterClause837 (baseVal q)

theorem counterClause838 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_left (literal (valuationOf q) (853)) (literal (valuationOf q) (864)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 1 (meaning853 q) (meaning864 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause838 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 864 = true := counterClause838 (baseVal q)

theorem counterClause839 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (860)) (literal (valuationOf q) (865)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 1 1 (meaning853 q) (meaning860 q) (meaning865 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause839 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 860 = false ∨ valuation q 865 = true := counterClause839 (baseVal q)

theorem counterClause840 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (861)) (literal (valuationOf q) (866)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 1 2 (meaning853 q) (meaning861 q) (meaning866 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause840 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 861 = false ∨ valuation q 866 = true := counterClause840 (baseVal q)

theorem counterClause841 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 862 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (862)) (literal (valuationOf q) (867)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 1 3 (meaning853 q) (meaning862 q) (meaning867 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 862 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause841 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 862 = false ∨ valuation q 867 = true := counterClause841 (baseVal q)

theorem counterClause842 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 863 = false ∨ valuationOf q 868 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (863)) (literal (valuationOf q) (868)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 1 4 (meaning853 q) (meaning863 q) (meaning868 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 863 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause842 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 863 = false ∨ valuation q 868 = true := counterClause842 (baseVal q)

theorem counterClause843 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_left (literal (valuationOf q) (854)) (literal (valuationOf q) (865)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 2 (meaning854 q) (meaning865 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause843 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 865 = true := counterClause843 (baseVal q)

theorem counterClause844 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (860)) (literal (valuationOf q) (866)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 2 1 (meaning854 q) (meaning860 q) (meaning866 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause844 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 860 = false ∨ valuation q 866 = true := counterClause844 (baseVal q)

theorem counterClause845 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (861)) (literal (valuationOf q) (867)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 2 2 (meaning854 q) (meaning861 q) (meaning867 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause845 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 861 = false ∨ valuation q 867 = true := counterClause845 (baseVal q)

theorem counterClause846 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 862 = false ∨ valuationOf q 868 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (862)) (literal (valuationOf q) (868)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 2 3 (meaning854 q) (meaning862 q) (meaning868 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 862 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause846 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 862 = false ∨ valuation q 868 = true := counterClause846 (baseVal q)

theorem counterClause847 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 863 = false ∨ valuationOf q 869 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (863)) (literal (valuationOf q) (869)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 2 4 (meaning854 q) (meaning863 q) (meaning869 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 863 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause847 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 863 = false ∨ valuation q 869 = true := counterClause847 (baseVal q)

theorem counterClause848 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_left (literal (valuationOf q) (855)) (literal (valuationOf q) (866)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 3 (meaning855 q) (meaning866 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause848 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 866 = true := counterClause848 (baseVal q)

theorem counterClause849 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 860 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (860)) (literal (valuationOf q) (867)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 3 1 (meaning855 q) (meaning860 q) (meaning867 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 860 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause849 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 860 = false ∨ valuation q 867 = true := counterClause849 (baseVal q)

theorem counterClause850 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (861)) (literal (valuationOf q) (868)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 3 2 (meaning855 q) (meaning861 q) (meaning868 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause850 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 861 = false ∨ valuation q 868 = true := counterClause850 (baseVal q)

theorem counterClause851 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 862 = false ∨ valuationOf q 869 = true := by
  have hs : count864 q = (countLit q [-27, -30, -33]) + (countLit q [-35, -37, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-27, -30, -33]) (l₂ := [-35, -37, -39, -40])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (862)) (literal (valuationOf q) (869)) (countLit q [-27, -30, -33]) (countLit q [-35, -37, -39, -40]) (count864 q) 3 3 (meaning855 q) (meaning862 q) (meaning869 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 862 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause851 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 862 = false ∨ valuation q 869 = true := counterClause851 (baseVal q)

theorem counterClause852 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_right (literal (valuationOf q) (-44)) (literal (valuationOf q) (871)) (countLit q [-42]) (countLit q [-44]) (count871 q) 1 (meaningNeg44 q) (meaning871 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause852 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 871 = true := counterClause852 (baseVal q)

theorem counterClause853 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_left (literal (valuationOf q) (-42)) (literal (valuationOf q) (871)) (countLit q [-42]) (countLit q [-44]) (count871 q) 1 (meaningNeg42 q) (meaning871 q) hs
  change (! (valuationOf q 42)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause853 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 871 = true := counterClause853 (baseVal q)

theorem counterClause854 (q : Nat → Bool) : valuationOf q 42 = true ∨ valuationOf q 44 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-42]) + (countLit q [-44]) := List.countP_append (p := literal q) (l₁ := [-42]) (l₂ := [-44])
  have hm := merge_two (literal (valuationOf q) (-42)) (literal (valuationOf q) (-44)) (literal (valuationOf q) (872)) (countLit q [-42]) (countLit q [-44]) (count871 q) 1 1 (meaningNeg42 q) (meaningNeg44 q) (meaning872 q) hs
  change (! (valuationOf q 42)) = false ∨ (! (valuationOf q 44)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause854 (q : Snake 81) (h : Conditions q) : valuation q 42 = true ∨ valuation q 44 = true ∨ valuation q 872 = true := counterClause854 (baseVal q)

theorem counterClause855 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_right (literal (valuationOf q) (-49)) (literal (valuationOf q) (873)) (countLit q [-46]) (countLit q [-49]) (count873 q) 1 (meaningNeg49 q) (meaning873 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause855 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 873 = true := counterClause855 (baseVal q)

theorem counterClause856 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (873)) (countLit q [-46]) (countLit q [-49]) (count873 q) 1 (meaningNeg46 q) (meaning873 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause856 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 873 = true := counterClause856 (baseVal q)

theorem counterClause857 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 49 = true ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-46]) + (countLit q [-49]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-49])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-49)) (literal (valuationOf q) (874)) (countLit q [-46]) (countLit q [-49]) (count873 q) 1 1 (meaningNeg46 q) (meaningNeg49 q) (meaning874 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 49)) = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause857 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 49 = true ∨ valuation q 874 = true := counterClause857 (baseVal q)

theorem counterClause858 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -49])
  have hm := merge_right (literal (valuationOf q) (873)) (literal (valuationOf q) (875)) (countLit q [-42, -44]) (countLit q [-46, -49]) (count875 q) 1 (meaning873 q) (meaning875 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause858 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 875 = true := counterClause858 (baseVal q)

theorem counterClause859 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -49])
  have hm := merge_right (literal (valuationOf q) (874)) (literal (valuationOf q) (876)) (countLit q [-42, -44]) (countLit q [-46, -49]) (count875 q) 2 (meaning874 q) (meaning876 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause859 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 876 = true := counterClause859 (baseVal q)

theorem counterClause860 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -49])
  have hm := merge_left (literal (valuationOf q) (871)) (literal (valuationOf q) (875)) (countLit q [-42, -44]) (countLit q [-46, -49]) (count875 q) 1 (meaning871 q) (meaning875 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause860 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 875 = true := counterClause860 (baseVal q)

theorem counterClause861 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 873 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (873)) (literal (valuationOf q) (876)) (countLit q [-42, -44]) (countLit q [-46, -49]) (count875 q) 1 1 (meaning871 q) (meaning873 q) (meaning876 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 873 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause861 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 873 = false ∨ valuation q 876 = true := counterClause861 (baseVal q)

theorem counterClause862 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 874 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (874)) (literal (valuationOf q) (877)) (countLit q [-42, -44]) (countLit q [-46, -49]) (count875 q) 1 2 (meaning871 q) (meaning874 q) (meaning877 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 874 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause862 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 874 = false ∨ valuation q 877 = true := counterClause862 (baseVal q)

theorem counterClause863 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -49])
  have hm := merge_left (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-42, -44]) (countLit q [-46, -49]) (count875 q) 2 (meaning872 q) (meaning876 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause863 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 876 = true := counterClause863 (baseVal q)

theorem counterClause864 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-42, -44]) + (countLit q [-46, -49]) := List.countP_append (p := literal q) (l₁ := [-42, -44]) (l₂ := [-46, -49])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (873)) (literal (valuationOf q) (877)) (countLit q [-42, -44]) (countLit q [-46, -49]) (count875 q) 2 1 (meaning872 q) (meaning873 q) (meaning877 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause864 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 873 = false ∨ valuation q 877 = true := counterClause864 (baseVal q)

theorem block26 (q : Snake 81) (h : Conditions q) : B112E213.Block26 (valuation q) :=
  ⟨clause833 q h, clause834 q h, clause835 q h, clause836 q h, clause837 q h, clause838 q h, clause839 q h, clause840 q h, clause841 q h, clause842 q h, clause843 q h, clause844 q h, clause845 q h, clause846 q h, clause847 q h, clause848 q h, clause849 q h, clause850 q h, clause851 q h, clause852 q h, clause853 q h, clause854 q h, clause855 q h, clause856 q h, clause857 q h, clause858 q h, clause859 q h, clause860 q h, clause861 q h, clause862 q h, clause863 q h, clause864 q h⟩

end
end Snake9.Regrowth.E112213
