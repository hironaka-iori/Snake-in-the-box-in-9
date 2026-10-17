import E112115Semantics
import B112E115Inputs
namespace Snake9.Regrowth.E112115
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 861 = true := by
  have hs : count860 q = (countLit q [-33, -38]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -38]) (l₂ := [-39, -40])
  have hm := merge_left (literal (valuationOf q) (857)) (literal (valuationOf q) (861)) (countLit q [-33, -38]) (countLit q [-39, -40]) (count860 q) 2 (meaning857 q) (meaning861 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 861 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 858 = false ∨ valuationOf q 862 = true := by
  have hs : count860 q = (countLit q [-33, -38]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -38]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (858)) (literal (valuationOf q) (862)) (countLit q [-33, -38]) (countLit q [-39, -40]) (count860 q) 2 1 (meaning857 q) (meaning858 q) (meaning862 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 858 = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 858 = false ∨ valuation q 862 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 859 = false ∨ valuationOf q 863 = true := by
  have hs : count860 q = (countLit q [-33, -38]) + (countLit q [-39, -40]) := List.countP_append (p := literal q) (l₁ := [-33, -38]) (l₂ := [-39, -40])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (859)) (literal (valuationOf q) (863)) (countLit q [-33, -38]) (countLit q [-39, -40]) (count860 q) 2 2 (meaning857 q) (meaning859 q) (meaning863 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 859 = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 859 = false ∨ valuation q 863 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 860 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_right (literal (valuationOf q) (860)) (literal (valuationOf q) (864)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 1 (meaning860 q) (meaning864 q) hs
  change valuationOf q 860 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 860 = false ∨ valuation q 864 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_right (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 2 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_right (literal (valuationOf q) (862)) (literal (valuationOf q) (866)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 3 (meaning862 q) (meaning866 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 866 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_right (literal (valuationOf q) (863)) (literal (valuationOf q) (867)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 4 (meaning863 q) (meaning867 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 867 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 864 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_left (literal (valuationOf q) (853)) (literal (valuationOf q) (864)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 1 (meaning853 q) (meaning864 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 864 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (860)) (literal (valuationOf q) (865)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 1 1 (meaning853 q) (meaning860 q) (meaning865 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 860 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 860 = false ∨ valuation q 865 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (861)) (literal (valuationOf q) (866)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 1 2 (meaning853 q) (meaning861 q) (meaning866 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 861 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 861 = false ∨ valuation q 866 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 853 = false ∨ valuationOf q 862 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_two (literal (valuationOf q) (853)) (literal (valuationOf q) (862)) (literal (valuationOf q) (867)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 1 3 (meaning853 q) (meaning862 q) (meaning867 q) hs
  change valuationOf q 853 = false ∨ valuationOf q 862 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 853 = false ∨ valuation q 862 = false ∨ valuation q 867 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 865 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_left (literal (valuationOf q) (854)) (literal (valuationOf q) (865)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 2 (meaning854 q) (meaning865 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 865 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (860)) (literal (valuationOf q) (866)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 2 1 (meaning854 q) (meaning860 q) (meaning866 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 860 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 860 = false ∨ valuation q 866 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (861)) (literal (valuationOf q) (867)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 2 2 (meaning854 q) (meaning861 q) (meaning867 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 861 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 861 = false ∨ valuation q 867 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 854 = false ∨ valuationOf q 862 = false ∨ valuationOf q 868 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_two (literal (valuationOf q) (854)) (literal (valuationOf q) (862)) (literal (valuationOf q) (868)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 2 3 (meaning854 q) (meaning862 q) (meaning868 q) hs
  change valuationOf q 854 = false ∨ valuationOf q 862 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 854 = false ∨ valuation q 862 = false ∨ valuation q 868 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 866 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_left (literal (valuationOf q) (855)) (literal (valuationOf q) (866)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 3 (meaning855 q) (meaning866 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 866 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 860 = false ∨ valuationOf q 867 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (860)) (literal (valuationOf q) (867)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 3 1 (meaning855 q) (meaning860 q) (meaning867 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 860 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 860 = false ∨ valuation q 867 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 855 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true := by
  have hs : count864 q = (countLit q [-28, -30, -32]) + (countLit q [-33, -38, -39, -40]) := List.countP_append (p := literal q) (l₁ := [-28, -30, -32]) (l₂ := [-33, -38, -39, -40])
  have hm := merge_two (literal (valuationOf q) (855)) (literal (valuationOf q) (861)) (literal (valuationOf q) (868)) (countLit q [-28, -30, -32]) (countLit q [-33, -38, -39, -40]) (count864 q) 3 2 (meaning855 q) (meaning861 q) (meaning868 q) hs
  change valuationOf q 855 = false ∨ valuationOf q 861 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 855 = false ∨ valuation q 861 = false ∨ valuation q 868 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_right (literal (valuationOf q) (-46)) (literal (valuationOf q) (871)) (countLit q [-43]) (countLit q [-46]) (count871 q) 1 (meaningNeg46 q) (meaning871 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 871 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-43)) (literal (valuationOf q) (871)) (countLit q [-43]) (countLit q [-46]) (count871 q) 1 (meaningNeg43 q) (meaning871 q) hs
  change (! (valuationOf q 43)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 871 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 43 = true ∨ valuationOf q 46 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-43]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-43]) (l₂ := [-46])
  have hm := merge_two (literal (valuationOf q) (-43)) (literal (valuationOf q) (-46)) (literal (valuationOf q) (872)) (countLit q [-43]) (countLit q [-46]) (count871 q) 1 1 (meaningNeg43 q) (meaningNeg46 q) (meaning872 q) hs
  change (! (valuationOf q 43)) = false ∨ (! (valuationOf q 46)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 43 = true ∨ valuation q 46 = true ∨ valuation q 872 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (873)) (countLit q [-48]) (countLit q [-50]) (count873 q) 1 (meaningNeg50 q) (meaning873 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 873 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (873)) (countLit q [-48]) (countLit q [-50]) (count873 q) 1 (meaningNeg48 q) (meaning873 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 873 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 50 = true ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (874)) (countLit q [-48]) (countLit q [-50]) (count873 q) 1 1 (meaningNeg48 q) (meaningNeg50 q) (meaning874 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 874 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-43, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-48, -50])
  have hm := merge_right (literal (valuationOf q) (873)) (literal (valuationOf q) (875)) (countLit q [-43, -46]) (countLit q [-48, -50]) (count875 q) 1 (meaning873 q) (meaning875 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 875 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-43, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-48, -50])
  have hm := merge_right (literal (valuationOf q) (874)) (literal (valuationOf q) (876)) (countLit q [-43, -46]) (countLit q [-48, -50]) (count875 q) 2 (meaning874 q) (meaning876 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 876 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 875 = true := by
  have hs : count875 q = (countLit q [-43, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-48, -50])
  have hm := merge_left (literal (valuationOf q) (871)) (literal (valuationOf q) (875)) (countLit q [-43, -46]) (countLit q [-48, -50]) (count875 q) 1 (meaning871 q) (meaning875 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 875 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 873 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-43, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (873)) (literal (valuationOf q) (876)) (countLit q [-43, -46]) (countLit q [-48, -50]) (count875 q) 1 1 (meaning871 q) (meaning873 q) (meaning876 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 873 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 873 = false ∨ valuation q 876 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 874 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-43, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (871)) (literal (valuationOf q) (874)) (literal (valuationOf q) (877)) (countLit q [-43, -46]) (countLit q [-48, -50]) (count875 q) 1 2 (meaning871 q) (meaning874 q) (meaning877 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 874 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 874 = false ∨ valuation q 877 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count875 q = (countLit q [-43, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-48, -50])
  have hm := merge_left (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-43, -46]) (countLit q [-48, -50]) (count875 q) 2 (meaning872 q) (meaning876 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 876 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true := by
  have hs : count875 q = (countLit q [-43, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (872)) (literal (valuationOf q) (873)) (literal (valuationOf q) (877)) (countLit q [-43, -46]) (countLit q [-48, -50]) (count875 q) 2 1 (meaning872 q) (meaning873 q) (meaning877 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 873 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 873 = false ∨ valuation q 877 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 879 = true := by
  have hs : count879 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (879)) (countLit q [-52]) (countLit q [-55]) (count879 q) 1 (meaningNeg55 q) (meaning879 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 879 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E115.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112115
