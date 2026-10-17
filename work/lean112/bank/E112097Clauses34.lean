import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec34 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1089 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 931 = false ∨ valuationOf q 942 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (931)) (literal (valuationOf q) (942)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 3 4 (meaning907 q) (meaning931 q) (meaning942 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 931 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1089 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 931 = false ∨ valuation q 942 = true := counterClause1089 (baseVal q)

theorem counterClause1090 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 932 = false ∨ valuationOf q 943 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (932)) (literal (valuationOf q) (943)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 3 5 (meaning907 q) (meaning932 q) (meaning943 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 932 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1090 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 932 = false ∨ valuation q 943 = true := counterClause1090 (baseVal q)

theorem counterClause1091 (q : Nat → Bool) : valuationOf q 907 = false ∨ valuationOf q 933 = false ∨ valuationOf q 944 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (907)) (literal (valuationOf q) (933)) (literal (valuationOf q) (944)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 3 6 (meaning907 q) (meaning933 q) (meaning944 q) hs
  change valuationOf q 907 = false ∨ valuationOf q 933 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1091 (q : Snake 81) (h : Conditions q) : valuation q 907 = false ∨ valuation q 933 = false ∨ valuation q 944 = true := counterClause1091 (baseVal q)

theorem counterClause1092 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 928 = false ∨ valuationOf q 940 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (928)) (literal (valuationOf q) (940)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 4 1 (meaning908 q) (meaning928 q) (meaning940 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 928 = false ∨ valuationOf q 940 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1092 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 928 = false ∨ valuation q 940 = true := counterClause1092 (baseVal q)

theorem counterClause1093 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 929 = false ∨ valuationOf q 941 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (929)) (literal (valuationOf q) (941)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 4 2 (meaning908 q) (meaning929 q) (meaning941 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 929 = false ∨ valuationOf q 941 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1093 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 929 = false ∨ valuation q 941 = true := counterClause1093 (baseVal q)

theorem counterClause1094 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 930 = false ∨ valuationOf q 942 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (930)) (literal (valuationOf q) (942)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 4 3 (meaning908 q) (meaning930 q) (meaning942 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 930 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1094 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 930 = false ∨ valuation q 942 = true := counterClause1094 (baseVal q)

theorem counterClause1095 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 931 = false ∨ valuationOf q 943 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (931)) (literal (valuationOf q) (943)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 4 4 (meaning908 q) (meaning931 q) (meaning943 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 931 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1095 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 931 = false ∨ valuation q 943 = true := counterClause1095 (baseVal q)

theorem counterClause1096 (q : Nat → Bool) : valuationOf q 908 = false ∨ valuationOf q 932 = false ∨ valuationOf q 944 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (908)) (literal (valuationOf q) (932)) (literal (valuationOf q) (944)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 4 5 (meaning908 q) (meaning932 q) (meaning944 q) hs
  change valuationOf q 908 = false ∨ valuationOf q 932 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1096 (q : Snake 81) (h : Conditions q) : valuation q 908 = false ∨ valuation q 932 = false ∨ valuation q 944 = true := counterClause1096 (baseVal q)

theorem counterClause1097 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 929 = false ∨ valuationOf q 942 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (929)) (literal (valuationOf q) (942)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 5 2 (meaning909 q) (meaning929 q) (meaning942 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 929 = false ∨ valuationOf q 942 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1097 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 929 = false ∨ valuation q 942 = true := counterClause1097 (baseVal q)

theorem counterClause1098 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 930 = false ∨ valuationOf q 943 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (930)) (literal (valuationOf q) (943)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 5 3 (meaning909 q) (meaning930 q) (meaning943 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 930 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1098 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 930 = false ∨ valuation q 943 = true := counterClause1098 (baseVal q)

theorem counterClause1099 (q : Nat → Bool) : valuationOf q 909 = false ∨ valuationOf q 932 = false ∨ valuationOf q 945 = true := by
  have hs : count936 q = (countLit q [-33, -34, -36, -38, -40, -43, -44]) + (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -38, -40, -43, -44]) (l₂ := [-46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (909)) (literal (valuationOf q) (932)) (literal (valuationOf q) (945)) (countLit q [-33, -34, -36, -38, -40, -43, -44]) (countLit q [-46, -47, -50, -53, -54, -55, -57, -59]) (count936 q) 5 5 (meaning909 q) (meaning932 q) (meaning945 q) hs
  change valuationOf q 909 = false ∨ valuationOf q 932 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1099 (q : Snake 81) (h : Conditions q) : valuation q 909 = false ∨ valuation q 932 = false ∨ valuation q 945 = true := counterClause1099 (baseVal q)

theorem counterClause1100 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 941 = false ∨ valuationOf q 959 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (941)) (literal (valuationOf q) (959)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 3 6 (meaning879 q) (meaning941 q) (meaning959 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 941 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1100 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 941 = false ∨ valuation q 959 = true := counterClause1100 (baseVal q)

theorem counterClause1101 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 942 = false ∨ valuationOf q 960 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (942)) (literal (valuationOf q) (960)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 3 7 (meaning879 q) (meaning942 q) (meaning960 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 942 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1101 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 942 = false ∨ valuation q 960 = true := counterClause1101 (baseVal q)

theorem counterClause1102 (q : Nat → Bool) : valuationOf q 879 = false ∨ valuationOf q 943 = false ∨ valuationOf q 961 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (879)) (literal (valuationOf q) (943)) (literal (valuationOf q) (961)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 3 8 (meaning879 q) (meaning943 q) (meaning961 q) hs
  change valuationOf q 879 = false ∨ valuationOf q 943 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1102 (q : Snake 81) (h : Conditions q) : valuation q 879 = false ∨ valuation q 943 = false ∨ valuation q 961 = true := counterClause1102 (baseVal q)

theorem counterClause1103 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 937 = false ∨ valuationOf q 956 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (937)) (literal (valuationOf q) (956)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 4 2 (meaning880 q) (meaning937 q) (meaning956 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 937 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1103 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 937 = false ∨ valuation q 956 = true := counterClause1103 (baseVal q)

theorem counterClause1104 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 938 = false ∨ valuationOf q 957 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (938)) (literal (valuationOf q) (957)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 4 3 (meaning880 q) (meaning938 q) (meaning957 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 938 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1104 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 938 = false ∨ valuation q 957 = true := counterClause1104 (baseVal q)

theorem counterClause1105 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 939 = false ∨ valuationOf q 958 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (939)) (literal (valuationOf q) (958)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 4 4 (meaning880 q) (meaning939 q) (meaning958 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 939 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1105 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 939 = false ∨ valuation q 958 = true := counterClause1105 (baseVal q)

theorem counterClause1106 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 940 = false ∨ valuationOf q 959 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (940)) (literal (valuationOf q) (959)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 4 5 (meaning880 q) (meaning940 q) (meaning959 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 940 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1106 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 940 = false ∨ valuation q 959 = true := counterClause1106 (baseVal q)

theorem counterClause1107 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 941 = false ∨ valuationOf q 960 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (941)) (literal (valuationOf q) (960)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 4 6 (meaning880 q) (meaning941 q) (meaning960 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 941 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1107 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 941 = false ∨ valuation q 960 = true := counterClause1107 (baseVal q)

theorem counterClause1108 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 942 = false ∨ valuationOf q 961 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (942)) (literal (valuationOf q) (961)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 4 7 (meaning880 q) (meaning942 q) (meaning961 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 942 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1108 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 942 = false ∨ valuation q 961 = true := counterClause1108 (baseVal q)

theorem counterClause1109 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 943 = false ∨ valuationOf q 962 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (943)) (literal (valuationOf q) (962)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 4 8 (meaning880 q) (meaning943 q) (meaning962 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 943 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1109 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 943 = false ∨ valuation q 962 = true := counterClause1109 (baseVal q)

theorem counterClause1110 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 944 = false ∨ valuationOf q 963 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (944)) (literal (valuationOf q) (963)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 4 9 (meaning880 q) (meaning944 q) (meaning963 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 944 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1110 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 944 = false ∨ valuation q 963 = true := counterClause1110 (baseVal q)

theorem counterClause1111 (q : Nat → Bool) : valuationOf q 880 = false ∨ valuationOf q 945 = false ∨ valuationOf q 964 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (880)) (literal (valuationOf q) (945)) (literal (valuationOf q) (964)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 4 10 (meaning880 q) (meaning945 q) (meaning964 q) hs
  change valuationOf q 880 = false ∨ valuationOf q 945 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1111 (q : Snake 81) (h : Conditions q) : valuation q 880 = false ∨ valuation q 945 = false ∨ valuation q 964 = true := counterClause1111 (baseVal q)

theorem counterClause1112 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 937 = false ∨ valuationOf q 957 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (937)) (literal (valuationOf q) (957)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 5 2 (meaning881 q) (meaning937 q) (meaning957 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 937 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1112 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 937 = false ∨ valuation q 957 = true := counterClause1112 (baseVal q)

theorem counterClause1113 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 938 = false ∨ valuationOf q 958 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (938)) (literal (valuationOf q) (958)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 5 3 (meaning881 q) (meaning938 q) (meaning958 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 938 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1113 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 938 = false ∨ valuation q 958 = true := counterClause1113 (baseVal q)

theorem counterClause1114 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 939 = false ∨ valuationOf q 959 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (939)) (literal (valuationOf q) (959)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 5 4 (meaning881 q) (meaning939 q) (meaning959 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 939 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1114 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 939 = false ∨ valuation q 959 = true := counterClause1114 (baseVal q)

theorem counterClause1115 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 940 = false ∨ valuationOf q 960 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (940)) (literal (valuationOf q) (960)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 5 5 (meaning881 q) (meaning940 q) (meaning960 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 940 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1115 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 940 = false ∨ valuation q 960 = true := counterClause1115 (baseVal q)

theorem counterClause1116 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 941 = false ∨ valuationOf q 961 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (941)) (literal (valuationOf q) (961)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 5 6 (meaning881 q) (meaning941 q) (meaning961 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 941 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1116 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 941 = false ∨ valuation q 961 = true := counterClause1116 (baseVal q)

theorem counterClause1117 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 942 = false ∨ valuationOf q 962 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (942)) (literal (valuationOf q) (962)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 5 7 (meaning881 q) (meaning942 q) (meaning962 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 942 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1117 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 942 = false ∨ valuation q 962 = true := counterClause1117 (baseVal q)

theorem counterClause1118 (q : Nat → Bool) : valuationOf q 881 = false ∨ valuationOf q 943 = false ∨ valuationOf q 963 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (881)) (literal (valuationOf q) (943)) (literal (valuationOf q) (963)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 5 8 (meaning881 q) (meaning943 q) (meaning963 q) hs
  change valuationOf q 881 = false ∨ valuationOf q 943 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1118 (q : Snake 81) (h : Conditions q) : valuation q 881 = false ∨ valuation q 943 = false ∨ valuation q 963 = true := counterClause1118 (baseVal q)

theorem counterClause1119 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 937 = false ∨ valuationOf q 958 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (937)) (literal (valuationOf q) (958)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 6 2 (meaning882 q) (meaning937 q) (meaning958 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 937 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1119 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 937 = false ∨ valuation q 958 = true := counterClause1119 (baseVal q)

theorem counterClause1120 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 938 = false ∨ valuationOf q 959 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (938)) (literal (valuationOf q) (959)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 6 3 (meaning882 q) (meaning938 q) (meaning959 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 938 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1120 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 938 = false ∨ valuation q 959 = true := counterClause1120 (baseVal q)

theorem block34 (q : Snake 81) (h : Conditions q) : B112E097.Block34 (valuation q) :=
  ⟨clause1089 q h, clause1090 q h, clause1091 q h, clause1092 q h, clause1093 q h, clause1094 q h, clause1095 q h, clause1096 q h, clause1097 q h, clause1098 q h, clause1099 q h, clause1100 q h, clause1101 q h, clause1102 q h, clause1103 q h, clause1104 q h, clause1105 q h, clause1106 q h, clause1107 q h, clause1108 q h, clause1109 q h, clause1110 q h, clause1111 q h, clause1112 q h, clause1113 q h, clause1114 q h, clause1115 q h, clause1116 q h, clause1117 q h, clause1118 q h, clause1119 q h, clause1120 q h⟩

end
end Snake9.Regrowth.E112097
