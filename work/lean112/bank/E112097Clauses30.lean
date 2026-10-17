import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 861 = false ∨ valuationOf q 864 = false ∨ valuationOf q 867 = true := by
  have hs : count865 q = (countLit q [-22, -25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-28, -29])
  have hm := merge_two (literal (valuationOf q) (861)) (literal (valuationOf q) (864)) (literal (valuationOf q) (867)) (countLit q [-22, -25]) (countLit q [-28, -29]) (count865 q) 1 2 (meaning861 q) (meaning864 q) (meaning867 q) hs
  change valuationOf q 861 = false ∨ valuationOf q 864 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 861 = false ∨ valuation q 864 = false ∨ valuation q 867 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 866 = true := by
  have hs : count865 q = (countLit q [-22, -25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-28, -29])
  have hm := merge_left (literal (valuationOf q) (862)) (literal (valuationOf q) (866)) (countLit q [-22, -25]) (countLit q [-28, -29]) (count865 q) 2 (meaning862 q) (meaning866 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 866 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 866 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 863 = false ∨ valuationOf q 867 = true := by
  have hs : count865 q = (countLit q [-22, -25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-28, -29])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (863)) (literal (valuationOf q) (867)) (countLit q [-22, -25]) (countLit q [-28, -29]) (count865 q) 2 1 (meaning862 q) (meaning863 q) (meaning867 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 863 = false ∨ valuationOf q 867 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 863 = false ∨ valuation q 867 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 862 = false ∨ valuationOf q 864 = false ∨ valuationOf q 868 = true := by
  have hs : count865 q = (countLit q [-22, -25]) + (countLit q [-28, -29]) := List.countP_append (p := literal q) (l₁ := [-22, -25]) (l₂ := [-28, -29])
  have hm := merge_two (literal (valuationOf q) (862)) (literal (valuationOf q) (864)) (literal (valuationOf q) (868)) (countLit q [-22, -25]) (countLit q [-28, -29]) (count865 q) 2 2 (meaning862 q) (meaning864 q) (meaning868 q) hs
  change valuationOf q 862 = false ∨ valuationOf q 864 = false ∨ valuationOf q 868 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 862 = false ∨ valuation q 864 = false ∨ valuation q 868 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 865 = false ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_right (literal (valuationOf q) (865)) (literal (valuationOf q) (869)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 1 (meaning865 q) (meaning869 q) hs
  change valuationOf q 865 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 865 = false ∨ valuation q 869 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 866 = false ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_right (literal (valuationOf q) (866)) (literal (valuationOf q) (870)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 2 (meaning866 q) (meaning870 q) hs
  change valuationOf q 866 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 866 = false ∨ valuation q 870 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 867 = false ∨ valuationOf q 871 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_right (literal (valuationOf q) (867)) (literal (valuationOf q) (871)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 3 (meaning867 q) (meaning871 q) hs
  change valuationOf q 867 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 867 = false ∨ valuation q 871 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 869 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_left (literal (valuationOf q) (857)) (literal (valuationOf q) (869)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 1 (meaning857 q) (meaning869 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 869 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 869 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 865 = false ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (865)) (literal (valuationOf q) (870)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 1 1 (meaning857 q) (meaning865 q) (meaning870 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 865 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 865 = false ∨ valuation q 870 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 866 = false ∨ valuationOf q 871 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (866)) (literal (valuationOf q) (871)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 1 2 (meaning857 q) (meaning866 q) (meaning871 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 866 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 866 = false ∨ valuation q 871 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 867 = false ∨ valuationOf q 872 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (867)) (literal (valuationOf q) (872)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 1 3 (meaning857 q) (meaning867 q) (meaning872 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 867 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 867 = false ∨ valuation q 872 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 857 = false ∨ valuationOf q 868 = false ∨ valuationOf q 873 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (857)) (literal (valuationOf q) (868)) (literal (valuationOf q) (873)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 1 4 (meaning857 q) (meaning868 q) (meaning873 q) hs
  change valuationOf q 857 = false ∨ valuationOf q 868 = false ∨ valuationOf q 873 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 857 = false ∨ valuation q 868 = false ∨ valuation q 873 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 870 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_left (literal (valuationOf q) (858)) (literal (valuationOf q) (870)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 2 (meaning858 q) (meaning870 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 870 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 870 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 865 = false ∨ valuationOf q 871 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (865)) (literal (valuationOf q) (871)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 2 1 (meaning858 q) (meaning865 q) (meaning871 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 865 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 865 = false ∨ valuation q 871 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 858 = false ∨ valuationOf q 866 = false ∨ valuationOf q 872 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (858)) (literal (valuationOf q) (866)) (literal (valuationOf q) (872)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 2 2 (meaning858 q) (meaning866 q) (meaning872 q) hs
  change valuationOf q 858 = false ∨ valuationOf q 866 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 858 = false ∨ valuation q 866 = false ∨ valuation q 872 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 871 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_left (literal (valuationOf q) (859)) (literal (valuationOf q) (871)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 3 (meaning859 q) (meaning871 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 871 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 871 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 859 = false ∨ valuationOf q 865 = false ∨ valuationOf q 872 = true := by
  have hs : count869 q = (countLit q [-13, -18, -20, -21]) + (countLit q [-22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-13, -18, -20, -21]) (l₂ := [-22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (859)) (literal (valuationOf q) (865)) (literal (valuationOf q) (872)) (countLit q [-13, -18, -20, -21]) (countLit q [-22, -25, -28, -29]) (count869 q) 3 1 (meaning859 q) (meaning865 q) (meaning872 q) hs
  change valuationOf q 859 = false ∨ valuationOf q 865 = false ∨ valuationOf q 872 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 859 = false ∨ valuation q 865 = false ∨ valuation q 872 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 879 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_left (literal (valuationOf q) (848)) (literal (valuationOf q) (879)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 3 (meaning848 q) (meaning879 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 879 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 879 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 869 = false ∨ valuationOf q 880 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (869)) (literal (valuationOf q) (880)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 3 1 (meaning848 q) (meaning869 q) (meaning880 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 869 = false ∨ valuationOf q 880 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 869 = false ∨ valuation q 880 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 870 = false ∨ valuationOf q 881 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (870)) (literal (valuationOf q) (881)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 3 2 (meaning848 q) (meaning870 q) (meaning881 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 870 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 870 = false ∨ valuation q 881 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 871 = false ∨ valuationOf q 882 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (871)) (literal (valuationOf q) (882)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 3 3 (meaning848 q) (meaning871 q) (meaning882 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 871 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 871 = false ∨ valuation q 882 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 872 = false ∨ valuationOf q 883 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (872)) (literal (valuationOf q) (883)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 3 4 (meaning848 q) (meaning872 q) (meaning883 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 872 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 872 = false ∨ valuation q 883 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 848 = false ∨ valuationOf q 873 = false ∨ valuationOf q 884 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (848)) (literal (valuationOf q) (873)) (literal (valuationOf q) (884)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 3 5 (meaning848 q) (meaning873 q) (meaning884 q) hs
  change valuationOf q 848 = false ∨ valuationOf q 873 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 848 = false ∨ valuation q 873 = false ∨ valuation q 884 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 869 = false ∨ valuationOf q 881 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (849)) (literal (valuationOf q) (869)) (literal (valuationOf q) (881)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 4 1 (meaning849 q) (meaning869 q) (meaning881 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 869 = false ∨ valuationOf q 881 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 869 = false ∨ valuation q 881 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 870 = false ∨ valuationOf q 882 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (849)) (literal (valuationOf q) (870)) (literal (valuationOf q) (882)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 4 2 (meaning849 q) (meaning870 q) (meaning882 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 870 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 870 = false ∨ valuation q 882 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 871 = false ∨ valuationOf q 883 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (849)) (literal (valuationOf q) (871)) (literal (valuationOf q) (883)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 4 3 (meaning849 q) (meaning871 q) (meaning883 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 871 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 871 = false ∨ valuation q 883 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 849 = false ∨ valuationOf q 872 = false ∨ valuationOf q 884 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (849)) (literal (valuationOf q) (872)) (literal (valuationOf q) (884)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 4 4 (meaning849 q) (meaning872 q) (meaning884 q) hs
  change valuationOf q 849 = false ∨ valuationOf q 872 = false ∨ valuationOf q 884 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 849 = false ∨ valuation q 872 = false ∨ valuation q 884 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 869 = false ∨ valuationOf q 882 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (850)) (literal (valuationOf q) (869)) (literal (valuationOf q) (882)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 5 1 (meaning850 q) (meaning869 q) (meaning882 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 869 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 869 = false ∨ valuation q 882 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 850 = false ∨ valuationOf q 870 = false ∨ valuationOf q 883 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (850)) (literal (valuationOf q) (870)) (literal (valuationOf q) (883)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 5 2 (meaning850 q) (meaning870 q) (meaning883 q) hs
  change valuationOf q 850 = false ∨ valuationOf q 870 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 850 = false ∨ valuation q 870 = false ∨ valuation q 883 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 882 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_left (literal (valuationOf q) (851)) (literal (valuationOf q) (882)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 6 (meaning851 q) (meaning882 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 882 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 882 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 851 = false ∨ valuationOf q 869 = false ∨ valuationOf q 883 = true := by
  have hs : count877 q = (countLit q [-1, -3, -4, -6, -7, -8, -10]) + (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10]) (l₂ := [-13, -18, -20, -21, -22, -25, -28, -29])
  have hm := merge_two (literal (valuationOf q) (851)) (literal (valuationOf q) (869)) (literal (valuationOf q) (883)) (countLit q [-1, -3, -4, -6, -7, -8, -10]) (countLit q [-13, -18, -20, -21, -22, -25, -28, -29]) (count877 q) 6 1 (meaning851 q) (meaning869 q) (meaning883 q) hs
  change valuationOf q 851 = false ∨ valuationOf q 869 = false ∨ valuationOf q 883 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 851 = false ∨ valuation q 869 = false ∨ valuation q 883 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 36 = true ∨ valuationOf q 892 = true := by
  have hs : count892 q = (countLit q [-34]) + (countLit q [-36]) := List.countP_append (p := literal q) (l₁ := [-34]) (l₂ := [-36])
  have hm := merge_right (literal (valuationOf q) (-36)) (literal (valuationOf q) (892)) (countLit q [-34]) (countLit q [-36]) (count892 q) 1 (meaningNeg36 q) (meaning892 q) hs
  change (! (valuationOf q 36)) = false ∨ valuationOf q 892 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 36 = true ∨ valuation q 892 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E097.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112097
