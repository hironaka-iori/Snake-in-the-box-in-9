import E112259Semantics
import B112E259Inputs
namespace Snake9.Regrowth.E112259
noncomputable section
local instance blockDec31 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause993 (q : Nat → Bool) : valuationOf q 845 = false ∨ valuationOf q 850 = false ∨ valuationOf q 857 = true := by
  have hs : count854 q = (countLit q [-30, -32, -34]) + (countLit q [-36, -38, -39, -42]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -34]) (l₂ := [-36, -38, -39, -42])
  have hm := merge_two (literal (valuationOf q) (845)) (literal (valuationOf q) (850)) (literal (valuationOf q) (857)) (countLit q [-30, -32, -34]) (countLit q [-36, -38, -39, -42]) (count854 q) 3 1 (meaning845 q) (meaning850 q) (meaning857 q) hs
  change valuationOf q 845 = false ∨ valuationOf q 850 = false ∨ valuationOf q 857 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause993 (q : Snake 81) (h : Conditions q) : valuation q 845 = false ∨ valuation q 850 = false ∨ valuation q 857 = true := counterClause993 (baseVal q)

theorem counterClause994 (q : Nat → Bool) : valuationOf q 44 = true ∨ valuationOf q 861 = true := by
  have hs : count861 q = (countLit q [-44]) + (countLit q [-46]) := List.countP_append (p := literal q) (l₁ := [-44]) (l₂ := [-46])
  have hm := merge_left (literal (valuationOf q) (-44)) (literal (valuationOf q) (861)) (countLit q [-44]) (countLit q [-46]) (count861 q) 1 (meaningNeg44 q) (meaning861 q) hs
  change (! (valuationOf q 44)) = false ∨ valuationOf q 861 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause994 (q : Snake 81) (h : Conditions q) : valuation q 44 = true ∨ valuation q 861 = true := counterClause994 (baseVal q)

theorem counterClause995 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_right (literal (valuationOf q) (-50)) (literal (valuationOf q) (863)) (countLit q [-48]) (countLit q [-50]) (count863 q) 1 (meaningNeg50 q) (meaning863 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause995 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 863 = true := counterClause995 (baseVal q)

theorem counterClause996 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 863 = true := by
  have hs : count863 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_left (literal (valuationOf q) (-48)) (literal (valuationOf q) (863)) (countLit q [-48]) (countLit q [-50]) (count863 q) 1 (meaningNeg48 q) (meaning863 q) hs
  change (! (valuationOf q 48)) = false ∨ valuationOf q 863 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause996 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 863 = true := counterClause996 (baseVal q)

theorem counterClause997 (q : Nat → Bool) : valuationOf q 48 = true ∨ valuationOf q 50 = true ∨ valuationOf q 864 = true := by
  have hs : count863 q = (countLit q [-48]) + (countLit q [-50]) := List.countP_append (p := literal q) (l₁ := [-48]) (l₂ := [-50])
  have hm := merge_two (literal (valuationOf q) (-48)) (literal (valuationOf q) (-50)) (literal (valuationOf q) (864)) (countLit q [-48]) (countLit q [-50]) (count863 q) 1 1 (meaningNeg48 q) (meaningNeg50 q) (meaning864 q) hs
  change (! (valuationOf q 48)) = false ∨ (! (valuationOf q 50)) = false ∨ valuationOf q 864 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause997 (q : Snake 81) (h : Conditions q) : valuation q 48 = true ∨ valuation q 50 = true ∨ valuation q 864 = true := counterClause997 (baseVal q)

theorem counterClause998 (q : Nat → Bool) : valuationOf q 863 = false ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-44, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -50])
  have hm := merge_right (literal (valuationOf q) (863)) (literal (valuationOf q) (865)) (countLit q [-44, -46]) (countLit q [-48, -50]) (count865 q) 1 (meaning863 q) (meaning865 q) hs
  change valuationOf q 863 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause998 (q : Snake 81) (h : Conditions q) : valuation q 863 = false ∨ valuation q 865 = true := counterClause998 (baseVal q)

theorem counterClause999 (q : Nat → Bool) : valuationOf q 864 = false ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-44, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -50])
  have hm := merge_right (literal (valuationOf q) (864)) (literal (valuationOf q) (866)) (countLit q [-44, -46]) (countLit q [-48, -50]) (count865 q) 2 (meaning864 q) (meaning866 q) hs
  change valuationOf q 864 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause999 (q : Snake 81) (h : Conditions q) : valuation q 864 = false ∨ valuation q 866 = true := counterClause999 (baseVal q)

theorem counterClause1000 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 865 = true := by
  have hs : count865 q = (countLit q [-44, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -50])
  have hm := merge_left (literal (valuationOf q) (861)) (literal (valuationOf q) (865)) (countLit q [-44, -46]) (countLit q [-48, -50]) (count865 q) 1 (meaning861 q) (meaning865 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 865 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1000 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 865 = true := counterClause1000 (baseVal q)

theorem counterClause1001 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-44, -46]) + (countLit q [-48, -50]) := List.countP_append (p := literal q) (l₁ := [-44, -46]) (l₂ := [-48, -50])
  have hm := merge_two (literal (valuationOf q) (861)) (literal (valuationOf q) (863)) (literal (valuationOf q) (866)) (countLit q [-44, -46]) (countLit q [-48, -50]) (count865 q) 1 1 (meaning861 q) (meaning863 q) (meaning866 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 863 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1001 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 863 = false ∨ valuation q 866 = true := counterClause1001 (baseVal q)

theorem counterClause1002 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_right (literal (valuationOf q) (-55)) (literal (valuationOf q) (869)) (countLit q [-52]) (countLit q [-55]) (count869 q) 1 (meaningNeg55 q) (meaning869 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1002 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 869 = true := counterClause1002 (baseVal q)

theorem counterClause1003 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_left (literal (valuationOf q) (-52)) (literal (valuationOf q) (869)) (countLit q [-52]) (countLit q [-55]) (count869 q) 1 (meaningNeg52 q) (meaning869 q) hs
  change (! (valuationOf q 52)) = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1003 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 869 = true := counterClause1003 (baseVal q)

theorem counterClause1004 (q : Nat → Bool) : valuationOf q 52 = true ∨ valuationOf q 55 = true ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-52]) + (countLit q [-55]) := List.countP_append (p := literal q) (l₁ := [-52]) (l₂ := [-55])
  have hm := merge_two (literal (valuationOf q) (-52)) (literal (valuationOf q) (-55)) (literal (valuationOf q) (870)) (countLit q [-52]) (countLit q [-55]) (count869 q) 1 1 (meaningNeg52 q) (meaningNeg55 q) (meaning870 q) hs
  change (! (valuationOf q 52)) = false ∨ (! (valuationOf q 55)) = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1004 (q : Snake 81) (h : Conditions q) : valuation q 52 = true ∨ valuation q 55 = true ∨ valuation q 870 = true := counterClause1004 (baseVal q)

theorem counterClause1005 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-57]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60])
  have hm := merge_right (literal (valuationOf q) (-60)) (literal (valuationOf q) (871)) (countLit q [-57]) (countLit q [-60]) (count871 q) 1 (meaningNeg60 q) (meaning871 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1005 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 871 = true := counterClause1005 (baseVal q)

theorem counterClause1006 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 871 = true := by
  have hs : count871 q = (countLit q [-57]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60])
  have hm := merge_left (literal (valuationOf q) (-57)) (literal (valuationOf q) (871)) (countLit q [-57]) (countLit q [-60]) (count871 q) 1 (meaningNeg57 q) (meaning871 q) hs
  change (! (valuationOf q 57)) = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1006 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 871 = true := counterClause1006 (baseVal q)

theorem counterClause1007 (q : Nat → Bool) : valuationOf q 57 = true ∨ valuationOf q 60 = true ∨ valuationOf q 872 = true := by
  have hs : count871 q = (countLit q [-57]) + (countLit q [-60]) := List.countP_append (p := literal q) (l₁ := [-57]) (l₂ := [-60])
  have hm := merge_two (literal (valuationOf q) (-57)) (literal (valuationOf q) (-60)) (literal (valuationOf q) (872)) (countLit q [-57]) (countLit q [-60]) (count871 q) 1 1 (meaningNeg57 q) (meaningNeg60 q) (meaning872 q) hs
  change (! (valuationOf q 57)) = false ∨ (! (valuationOf q 60)) = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1007 (q : Snake 81) (h : Conditions q) : valuation q 57 = true ∨ valuation q 60 = true ∨ valuation q 872 = true := counterClause1007 (baseVal q)

theorem counterClause1008 (q : Nat → Bool) : valuationOf q 871 = false ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-52, -55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-57, -60])
  have hm := merge_right (literal (valuationOf q) (871)) (literal (valuationOf q) (873)) (countLit q [-52, -55]) (countLit q [-57, -60]) (count873 q) 1 (meaning871 q) (meaning873 q) hs
  change valuationOf q 871 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1008 (q : Snake 81) (h : Conditions q) : valuation q 871 = false ∨ valuation q 873 = true := counterClause1008 (baseVal q)

theorem counterClause1009 (q : Nat → Bool) : valuationOf q 872 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-52, -55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-57, -60])
  have hm := merge_right (literal (valuationOf q) (872)) (literal (valuationOf q) (874)) (countLit q [-52, -55]) (countLit q [-57, -60]) (count873 q) 2 (meaning872 q) (meaning874 q) hs
  change valuationOf q 872 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1009 (q : Snake 81) (h : Conditions q) : valuation q 872 = false ∨ valuation q 874 = true := counterClause1009 (baseVal q)

theorem counterClause1010 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 873 = true := by
  have hs : count873 q = (countLit q [-52, -55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-57, -60])
  have hm := merge_left (literal (valuationOf q) (869)) (literal (valuationOf q) (873)) (countLit q [-52, -55]) (countLit q [-57, -60]) (count873 q) 1 (meaning869 q) (meaning873 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1010 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 873 = true := counterClause1010 (baseVal q)

theorem counterClause1011 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 871 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-52, -55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-57, -60])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (871)) (literal (valuationOf q) (874)) (countLit q [-52, -55]) (countLit q [-57, -60]) (count873 q) 1 1 (meaning869 q) (meaning871 q) (meaning874 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 871 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1011 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 871 = false ∨ valuation q 874 = true := counterClause1011 (baseVal q)

theorem counterClause1012 (q : Nat → Bool) : valuationOf q 869 = false ∨ valuationOf q 872 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-52, -55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-57, -60])
  have hm := merge_two (literal (valuationOf q) (869)) (literal (valuationOf q) (872)) (literal (valuationOf q) (875)) (countLit q [-52, -55]) (countLit q [-57, -60]) (count873 q) 1 2 (meaning869 q) (meaning872 q) (meaning875 q) hs
  change valuationOf q 869 = false ∨ valuationOf q 872 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1012 (q : Snake 81) (h : Conditions q) : valuation q 869 = false ∨ valuation q 872 = false ∨ valuation q 875 = true := counterClause1012 (baseVal q)

theorem counterClause1013 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 874 = true := by
  have hs : count873 q = (countLit q [-52, -55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-57, -60])
  have hm := merge_left (literal (valuationOf q) (870)) (literal (valuationOf q) (874)) (countLit q [-52, -55]) (countLit q [-57, -60]) (count873 q) 2 (meaning870 q) (meaning874 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 874 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1013 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 874 = true := counterClause1013 (baseVal q)

theorem counterClause1014 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 871 = false ∨ valuationOf q 875 = true := by
  have hs : count873 q = (countLit q [-52, -55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-57, -60])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (871)) (literal (valuationOf q) (875)) (countLit q [-52, -55]) (countLit q [-57, -60]) (count873 q) 2 1 (meaning870 q) (meaning871 q) (meaning875 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 871 = false ∨ valuationOf q 875 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1014 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 871 = false ∨ valuation q 875 = true := counterClause1014 (baseVal q)

theorem counterClause1015 (q : Nat → Bool) : valuationOf q 870 = false ∨ valuationOf q 872 = false ∨ valuationOf q 876 = true := by
  have hs : count873 q = (countLit q [-52, -55]) + (countLit q [-57, -60]) := List.countP_append (p := literal q) (l₁ := [-52, -55]) (l₂ := [-57, -60])
  have hm := merge_two (literal (valuationOf q) (870)) (literal (valuationOf q) (872)) (literal (valuationOf q) (876)) (countLit q [-52, -55]) (countLit q [-57, -60]) (count873 q) 2 2 (meaning870 q) (meaning872 q) (meaning876 q) hs
  change valuationOf q 870 = false ∨ valuationOf q 872 = false ∨ valuationOf q 876 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1015 (q : Snake 81) (h : Conditions q) : valuation q 870 = false ∨ valuation q 872 = false ∨ valuation q 876 = true := counterClause1015 (baseVal q)

theorem counterClause1016 (q : Nat → Bool) : valuationOf q 873 = false ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_right (literal (valuationOf q) (873)) (literal (valuationOf q) (877)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 1 (meaning873 q) (meaning877 q) hs
  change valuationOf q 873 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1016 (q : Snake 81) (h : Conditions q) : valuation q 873 = false ∨ valuation q 877 = true := counterClause1016 (baseVal q)

theorem counterClause1017 (q : Nat → Bool) : valuationOf q 874 = false ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_right (literal (valuationOf q) (874)) (literal (valuationOf q) (878)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 2 (meaning874 q) (meaning878 q) hs
  change valuationOf q 874 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1017 (q : Snake 81) (h : Conditions q) : valuation q 874 = false ∨ valuation q 878 = true := counterClause1017 (baseVal q)

theorem counterClause1018 (q : Nat → Bool) : valuationOf q 875 = false ∨ valuationOf q 879 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_right (literal (valuationOf q) (875)) (literal (valuationOf q) (879)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 3 (meaning875 q) (meaning879 q) hs
  change valuationOf q 875 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1018 (q : Snake 81) (h : Conditions q) : valuation q 875 = false ∨ valuation q 879 = true := counterClause1018 (baseVal q)

theorem counterClause1019 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 877 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_left (literal (valuationOf q) (865)) (literal (valuationOf q) (877)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 1 (meaning865 q) (meaning877 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 877 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1019 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 877 = true := counterClause1019 (baseVal q)

theorem counterClause1020 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 873 = false ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (873)) (literal (valuationOf q) (878)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 1 1 (meaning865 q) (meaning873 q) (meaning878 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 873 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1020 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 873 = false ∨ valuation q 878 = true := counterClause1020 (baseVal q)

theorem counterClause1021 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 874 = false ∨ valuationOf q 879 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (874)) (literal (valuationOf q) (879)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 1 2 (meaning865 q) (meaning874 q) (meaning879 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 874 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1021 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 874 = false ∨ valuation q 879 = true := counterClause1021 (baseVal q)

theorem counterClause1022 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 875 = false ∨ valuationOf q 880 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (875)) (literal (valuationOf q) (880)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 1 3 (meaning865 q) (meaning875 q) (meaning880 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 875 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1022 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 875 = false ∨ valuation q 880 = true := counterClause1022 (baseVal q)

theorem counterClause1023 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_two (literal (valuationOf q) (865)) (literal (valuationOf q) (876)) (literal (valuationOf q) (881)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 1 4 (meaning865 q) (meaning876 q) (meaning881 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 876 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1023 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 876 = false ∨ valuation q 881 = true := counterClause1023 (baseVal q)

theorem counterClause1024 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 878 = true := by
  have hs : count877 q = (countLit q [-44, -46, -48, -50]) + (countLit q [-52, -55, -57, -60]) := List.countP_append (p := literal q) (l₁ := [-44, -46, -48, -50]) (l₂ := [-52, -55, -57, -60])
  have hm := merge_left (literal (valuationOf q) (866)) (literal (valuationOf q) (878)) (countLit q [-44, -46, -48, -50]) (countLit q [-52, -55, -57, -60]) (count877 q) 2 (meaning866 q) (meaning878 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 878 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1024 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 878 = true := counterClause1024 (baseVal q)

theorem block31 (q : Snake 81) (h : Conditions q) : B112E259.Block31 (valuation q) :=
  ⟨clause993 q h, clause994 q h, clause995 q h, clause996 q h, clause997 q h, clause998 q h, clause999 q h, clause1000 q h, clause1001 q h, clause1002 q h, clause1003 q h, clause1004 q h, clause1005 q h, clause1006 q h, clause1007 q h, clause1008 q h, clause1009 q h, clause1010 q h, clause1011 q h, clause1012 q h, clause1013 q h, clause1014 q h, clause1015 q h, clause1016 q h, clause1017 q h, clause1018 q h, clause1019 q h, clause1020 q h, clause1021 q h, clause1022 q h, clause1023 q h, clause1024 q h⟩

end
end Snake9.Regrowth.E112259
