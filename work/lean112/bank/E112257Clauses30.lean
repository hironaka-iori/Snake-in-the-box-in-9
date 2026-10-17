import E112257Semantics
import B112E257Inputs
namespace Snake9.Regrowth.E112257
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 850 = false ∨ valuationOf q 857 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (850)) (literal (valuationOf q) (857)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 3 1 (meaning845 q) (meaning850 q) (meaning857 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 850 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 850 = false ∨ valuation q 857 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 851 = false ∨ valuationOf q 858 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-40, -42, -44, -45]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-40, -42, -44, -45])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (851)) (literal (valuationOf q) (858)) (countLit q [-30, -32, -34]) (countLit q [-40, -42, -44, -45]) (count854 q) 3 2 (meaning845 q) (meaning851 q) (meaning858 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 851 = false ∨ valuationOf q 858 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 851 = false ∨ valuation q 858 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 861 = true := by
  have hs : count861 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_right (literal (valuationOf q) (-48)) (literal (valuationOf q) (861)) (countLit q [-46]) (countLit q [-48]) (count861 q) 1 (meaningNeg48 q) (meaning861 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 861 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 861 = true := by
  have hs : count861 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_left (literal (valuationOf q) (-46)) (literal (valuationOf q) (861)) (countLit q [-46]) (countLit q [-48]) (count861 q) 1 (meaningNeg46 q) (meaning861 q) hs
  change (! (valuationOf q 46)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 861 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 46 = true ∨ valuationOf q 48 = true ∨ valuationOf q 862 = true := by
  have hs : count861 q = (countLit q [-46]) + (countLit q [-48]) := List.countP_append (p := literal q) (l₁ := [-46]) (l₂ := [-48])
  have hm := merge_two (literal (valuationOf q) (-46)) (literal (valuationOf q) (-48)) (literal (valuationOf q) (862)) (countLit q [-46]) (countLit q [-48]) (count861 q) 1 1 (meaningNeg46 q) (meaningNeg48 q) (meaning862 q) hs
  change (! (valuationOf q 46)) = false ∨ (! (valuationOf q 48)) = false ∨ valuationOf q 862 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 46 = true ∨ valuation q 48 = true ∨ valuation q 862 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (863)) (countLit q [-49]) (countLit q [-50]) (count863 q) 1 (meaningNeg50 q) (meaning863 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 863 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-49)) (literal (valuationOf q) (863)) (countLit q [-49]) (countLit q [-50]) (count863 q) 1 (meaningNeg49 q) (meaning863 q) hs
  change (! (valuationOf q 49)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 863 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 49 = true ∨ valuationOf q 50 = true ∨ valuationOf q 864 = true := by
  have hs : count863 q = (countLit q [-49]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-49]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-49)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (864)) (countLit q [-49]) (countLit q [-50]) (count863 q) 1 1 (meaningNeg49 q) (meaningNeg50 q) (meaning864 q) hs
  change (! (valuationOf q 49)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 49 = true ∨ valuation q 50 = true ∨ valuation q 864 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-46, -48]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -50])
  have hm := merge_right (literal (valuationOf q) (863)) (literal (valuationOf q) (865)) (countLit q [-46, -48]) (countLit q [-49, -50]) (count865 q) 1 (meaning863 q) (meaning865 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 865 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-46, -48]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -50])
  have hm := merge_right (literal (valuationOf q) (864)) (literal (valuationOf q) (866)) (countLit q [-46, -48]) (countLit q [-49, -50]) (count865 q) 2 (meaning864 q) (meaning866 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 866 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-46, -48]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -50])
  have hm := merge_left (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-46, -48]) (countLit q [-49, -50]) (count865 q) 1 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-46, -48]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -50])
  have hm := merge_two (literal (valuationOf q) (861)) (literal (valuationOf q) (863)) (literal (valuationOf q) (866)) (countLit q [-46, -48]) (countLit q [-49, -50]) (count865 q) 1 1 (meaning861 q) (meaning863 q) (meaning866 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 863 = false ∨ valuation q 866 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 864 = false ∨ valuationOf q 867 = true := by
  have hs : count865 q = (countLit q [-46, -48]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -50])
  have hm := merge_two (literal (valuationOf q) (861)) (literal (valuationOf q) (864)) (literal (valuationOf q) (867)) (countLit q [-46, -48]) (countLit q [-49, -50]) (count865 q) 1 2 (meaning861 q) (meaning864 q) (meaning867 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 864 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 864 = false ∨ valuation q 867 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-46, -48]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -50])
  have hm := merge_left (literal (valuationOf q) (862)) (literal (valuationOf q) (866)) (countLit q [-46, -48]) (countLit q [-49, -50]) (count865 q) 2 (meaning862 q) (meaning866 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 866 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 863 = false ∨ valuationOf q 867 = true := by
  have hs : count865 q = (countLit q [-46, -48]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -50])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (863)) (literal (valuationOf q) (867)) (countLit q [-46, -48]) (countLit q [-49, -50]) (count865 q) 2 1 (meaning862 q) (meaning863 q) (meaning867 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 863 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 863 = false ∨ valuation q 867 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 864 = false ∨ valuationOf q 868 = true := by
  have hs : count865 q = (countLit q [-46, -48]) + (countLit q [-49, -50]) := List.countP_append (p := literal q) (l₁ := [-46, -48]) (l₂ := [-49, -50])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (864)) (literal (valuationOf q) (868)) (countLit q [-46, -48]) (countLit q [-49, -50]) (count865 q) 2 2 (meaning862 q) (meaning864 q) (meaning868 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 864 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 864 = false ∨ valuation q 868 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_right (literal (valuationOf q) (-54)) (literal (valuationOf q) (869)) (countLit q [-52]) (countLit q [-54]) (count869 q) 1 (meaningNeg54 q) (meaning869 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 869 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (869)) (countLit q [-52]) (countLit q [-54]) (count869 q) 1 (meaningNeg52 q) (meaning869 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 869 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 54 = true ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-52]) + (countLit q [-54]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-54])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-54)) (literal (valuationOf q) (870)) (countLit q [-52]) (countLit q [-54]) (count869 q) 1 1 (meaningNeg52 q) (meaningNeg54 q) (meaning870 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 54)) = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 54 = true ∨ valuation q 870 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (871)) (countLit q [-59]) (countLit q [-60]) (count871 q) 1 (meaningNeg60 q) (meaning871 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 871 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-59)) (literal (valuationOf q) (871)) (countLit q [-59]) (countLit q [-60]) (count871 q) 1 (meaningNeg59 q) (meaning871 q) hs
  change (! (valuationOf q 59)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 871 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 59 = true ∨ valuationOf q 60 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-59]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-59]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-59)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (872)) (countLit q [-59]) (countLit q [-60]) (count871 q) 1 1 (meaningNeg59 q) (meaningNeg60 q) (meaning872 q) hs
  change (! (valuationOf q 59)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 59 = true ∨ valuation q 60 = true ∨ valuation q 872 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-52, -54]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (871)) (literal (valuationOf q) (873)) (countLit q [-52, -54]) (countLit q [-59, -60]) (count873 q) 1 (meaning871 q) (meaning873 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 873 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-52, -54]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-59, -60])
  have hm := merge_right (literal (valuationOf q) (872)) (literal (valuationOf q) (874)) (countLit q [-52, -54]) (countLit q [-59, -60]) (count873 q) 2 (meaning872 q) (meaning874 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 874 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-52, -54]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuationOf q) (869)) (literal (valuationOf q) (873)) (countLit q [-52, -54]) (countLit q [-59, -60]) (count873 q) 1 (meaning869 q) (meaning873 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 873 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 871 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-52, -54]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (871)) (literal (valuationOf q) (874)) (countLit q [-52, -54]) (countLit q [-59, -60]) (count873 q) 1 1 (meaning869 q) (meaning871 q) (meaning874 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 871 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 871 = false ∨ valuation q 874 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 872 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-52, -54]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (872)) (literal (valuationOf q) (875)) (countLit q [-52, -54]) (countLit q [-59, -60]) (count873 q) 1 2 (meaning869 q) (meaning872 q) (meaning875 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 872 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 872 = false ∨ valuation q 875 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-52, -54]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-59, -60])
  have hm := merge_left (literal (valuationOf q) (870)) (literal (valuationOf q) (874)) (countLit q [-52, -54]) (countLit q [-59, -60]) (count873 q) 2 (meaning870 q) (meaning874 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 874 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 871 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-52, -54]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (871)) (literal (valuationOf q) (875)) (countLit q [-52, -54]) (countLit q [-59, -60]) (count873 q) 2 1 (meaning870 q) (meaning871 q) (meaning875 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 871 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 871 = false ∨ valuation q 875 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count873 q = (countLit q [-52, -54]) + (countLit q [-59, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -54]) (l₂ := [-59, -60])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-52, -54]) (countLit q [-59, -60]) (count873 q) 2 2 (meaning870 q) (meaning872 q) (meaning876 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 872 = false ∨ valuation q 876 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (873)) (literal (valuationOf q) (877)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 1 (meaning873 q) (meaning877 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 877 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-46, -48, -49, -50]) + (countLit q [-52, -54, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-46, -48, -49, -50]) (l₂ := [-52, -54, -59, -60])
  have hm := merge_right (literal (valuationOf q) (874)) (literal (valuationOf q) (878)) (countLit q [-46, -48, -49, -50]) (countLit q [-52, -54, -59, -60]) (count877 q) 2 (meaning874 q) (meaning878 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 878 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E257.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112257
