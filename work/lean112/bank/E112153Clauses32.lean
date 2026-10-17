import E112153Semantics
import B112E153Inputs
namespace Snake9.Regrowth.E112153
noncomputable section
local instance blockDec32 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1025 (q : Nat → Bool) : valuationOf q 918 = false ∨ valuationOf q 946 = false ∨ valuationOf q 955 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (918)) (literal (valuationOf q) (946)) (literal (valuationOf q) (955)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 1 5 (meaning918 q) (meaning946 q) (meaning955 q) hs
  change valuationOf q 918 = false ∨ valuationOf q 946 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1025 (q : Snake 81) (h : Conditions q) : valuation q 918 = false ∨ valuation q 946 = false ∨ valuation q 955 = true := counterClause1025 (baseVal q)

theorem counterClause1026 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 943 = false ∨ valuationOf q 953 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (943)) (literal (valuationOf q) (953)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 2 2 (meaning919 q) (meaning943 q) (meaning953 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 943 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1026 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 943 = false ∨ valuation q 953 = true := counterClause1026 (baseVal q)

theorem counterClause1027 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 944 = false ∨ valuationOf q 954 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (944)) (literal (valuationOf q) (954)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 2 3 (meaning919 q) (meaning944 q) (meaning954 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 944 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1027 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 944 = false ∨ valuation q 954 = true := counterClause1027 (baseVal q)

theorem counterClause1028 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 945 = false ∨ valuationOf q 955 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (945)) (literal (valuationOf q) (955)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 2 4 (meaning919 q) (meaning945 q) (meaning955 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 945 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1028 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 945 = false ∨ valuation q 955 = true := counterClause1028 (baseVal q)

theorem counterClause1029 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 946 = false ∨ valuationOf q 956 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (946)) (literal (valuationOf q) (956)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 2 5 (meaning919 q) (meaning946 q) (meaning956 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 946 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1029 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 946 = false ∨ valuation q 956 = true := counterClause1029 (baseVal q)

theorem counterClause1030 (q : Nat → Bool) : valuationOf q 919 = false ∨ valuationOf q 947 = false ∨ valuationOf q 957 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (919)) (literal (valuationOf q) (947)) (literal (valuationOf q) (957)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 2 6 (meaning919 q) (meaning947 q) (meaning957 q) hs
  change valuationOf q 919 = false ∨ valuationOf q 947 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1030 (q : Snake 81) (h : Conditions q) : valuation q 919 = false ∨ valuation q 947 = false ∨ valuation q 957 = true := counterClause1030 (baseVal q)

theorem counterClause1031 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 942 = false ∨ valuationOf q 953 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (942)) (literal (valuationOf q) (953)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 3 1 (meaning920 q) (meaning942 q) (meaning953 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 942 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1031 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 942 = false ∨ valuation q 953 = true := counterClause1031 (baseVal q)

theorem counterClause1032 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 943 = false ∨ valuationOf q 954 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (943)) (literal (valuationOf q) (954)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 3 2 (meaning920 q) (meaning943 q) (meaning954 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 943 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1032 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 943 = false ∨ valuation q 954 = true := counterClause1032 (baseVal q)

theorem counterClause1033 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 944 = false ∨ valuationOf q 955 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (944)) (literal (valuationOf q) (955)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 3 3 (meaning920 q) (meaning944 q) (meaning955 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 944 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1033 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 944 = false ∨ valuation q 955 = true := counterClause1033 (baseVal q)

theorem counterClause1034 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 945 = false ∨ valuationOf q 956 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (945)) (literal (valuationOf q) (956)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 3 4 (meaning920 q) (meaning945 q) (meaning956 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 945 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1034 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 945 = false ∨ valuation q 956 = true := counterClause1034 (baseVal q)

theorem counterClause1035 (q : Nat → Bool) : valuationOf q 920 = false ∨ valuationOf q 946 = false ∨ valuationOf q 957 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (920)) (literal (valuationOf q) (946)) (literal (valuationOf q) (957)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 3 5 (meaning920 q) (meaning946 q) (meaning957 q) hs
  change valuationOf q 920 = false ∨ valuationOf q 946 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1035 (q : Snake 81) (h : Conditions q) : valuation q 920 = false ∨ valuation q 946 = false ∨ valuation q 957 = true := counterClause1035 (baseVal q)

theorem counterClause1036 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 942 = false ∨ valuationOf q 954 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (942)) (literal (valuationOf q) (954)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 4 1 (meaning921 q) (meaning942 q) (meaning954 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 942 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1036 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 942 = false ∨ valuation q 954 = true := counterClause1036 (baseVal q)

theorem counterClause1037 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 943 = false ∨ valuationOf q 955 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (943)) (literal (valuationOf q) (955)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 4 2 (meaning921 q) (meaning943 q) (meaning955 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 943 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1037 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 943 = false ∨ valuation q 955 = true := counterClause1037 (baseVal q)

theorem counterClause1038 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 944 = false ∨ valuationOf q 956 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (944)) (literal (valuationOf q) (956)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 4 3 (meaning921 q) (meaning944 q) (meaning956 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 944 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1038 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 944 = false ∨ valuation q 956 = true := counterClause1038 (baseVal q)

theorem counterClause1039 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 945 = false ∨ valuationOf q 957 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (945)) (literal (valuationOf q) (957)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 4 4 (meaning921 q) (meaning945 q) (meaning957 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 945 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1039 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 945 = false ∨ valuation q 957 = true := counterClause1039 (baseVal q)

theorem counterClause1040 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 943 = false ∨ valuationOf q 956 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (943)) (literal (valuationOf q) (956)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 5 2 (meaning922 q) (meaning943 q) (meaning956 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 943 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1040 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 943 = false ∨ valuation q 956 = true := counterClause1040 (baseVal q)

theorem counterClause1041 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 945 = false ∨ valuationOf q 958 = true := by
  have hs : count950 q = (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) + (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-32, -35, -37, -38, -39, -43, -45, -46]) (l₂ := [-47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (945)) (literal (valuationOf q) (958)) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46]) (countLit q [-47, -51, -52, -53, -55, -57, -60, -61]) (count950 q) 5 4 (meaning922 q) (meaning945 q) (meaning958 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 945 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1041 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 945 = false ∨ valuation q 958 = true := counterClause1041 (baseVal q)

theorem counterClause1042 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 952 = false ∨ valuationOf q 971 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (952)) (literal (valuationOf q) (971)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 3 3 (meaning889 q) (meaning952 q) (meaning971 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 952 = false ∨ valuationOf q 971 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1042 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 952 = false ∨ valuation q 971 = true := counterClause1042 (baseVal q)

theorem counterClause1043 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 953 = false ∨ valuationOf q 972 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (953)) (literal (valuationOf q) (972)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 3 4 (meaning889 q) (meaning953 q) (meaning972 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 953 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1043 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 953 = false ∨ valuation q 972 = true := counterClause1043 (baseVal q)

theorem counterClause1044 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 954 = false ∨ valuationOf q 973 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (954)) (literal (valuationOf q) (973)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 3 5 (meaning889 q) (meaning954 q) (meaning973 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 954 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1044 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 954 = false ∨ valuation q 973 = true := counterClause1044 (baseVal q)

theorem counterClause1045 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 955 = false ∨ valuationOf q 974 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (955)) (literal (valuationOf q) (974)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 3 6 (meaning889 q) (meaning955 q) (meaning974 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 955 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1045 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 955 = false ∨ valuation q 974 = true := counterClause1045 (baseVal q)

theorem counterClause1046 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 956 = false ∨ valuationOf q 975 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (956)) (literal (valuationOf q) (975)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 3 7 (meaning889 q) (meaning956 q) (meaning975 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 956 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1046 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 956 = false ∨ valuation q 975 = true := counterClause1046 (baseVal q)

theorem counterClause1047 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 957 = false ∨ valuationOf q 976 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (957)) (literal (valuationOf q) (976)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 3 8 (meaning889 q) (meaning957 q) (meaning976 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 957 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1047 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 957 = false ∨ valuation q 976 = true := counterClause1047 (baseVal q)

theorem counterClause1048 (q : Nat → Bool) : valuationOf q 889 = false ∨ valuationOf q 958 = false ∨ valuationOf q 977 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (889)) (literal (valuationOf q) (958)) (literal (valuationOf q) (977)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 3 9 (meaning889 q) (meaning958 q) (meaning977 q) hs
  change valuationOf q 889 = false ∨ valuationOf q 958 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1048 (q : Snake 81) (h : Conditions q) : valuation q 889 = false ∨ valuation q 958 = false ∨ valuation q 977 = true := counterClause1048 (baseVal q)

theorem counterClause1049 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 952 = false ∨ valuationOf q 972 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (890)) (literal (valuationOf q) (952)) (literal (valuationOf q) (972)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 4 3 (meaning890 q) (meaning952 q) (meaning972 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 952 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1049 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 952 = false ∨ valuation q 972 = true := counterClause1049 (baseVal q)

theorem counterClause1050 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 953 = false ∨ valuationOf q 973 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (890)) (literal (valuationOf q) (953)) (literal (valuationOf q) (973)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 4 4 (meaning890 q) (meaning953 q) (meaning973 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 953 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1050 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 953 = false ∨ valuation q 973 = true := counterClause1050 (baseVal q)

theorem counterClause1051 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 954 = false ∨ valuationOf q 974 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (890)) (literal (valuationOf q) (954)) (literal (valuationOf q) (974)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 4 5 (meaning890 q) (meaning954 q) (meaning974 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 954 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1051 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 954 = false ∨ valuation q 974 = true := counterClause1051 (baseVal q)

theorem counterClause1052 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 955 = false ∨ valuationOf q 975 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (890)) (literal (valuationOf q) (955)) (literal (valuationOf q) (975)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 4 6 (meaning890 q) (meaning955 q) (meaning975 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 955 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1052 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 955 = false ∨ valuation q 975 = true := counterClause1052 (baseVal q)

theorem counterClause1053 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 956 = false ∨ valuationOf q 976 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (890)) (literal (valuationOf q) (956)) (literal (valuationOf q) (976)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 4 7 (meaning890 q) (meaning956 q) (meaning976 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 956 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1053 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 956 = false ∨ valuation q 976 = true := counterClause1053 (baseVal q)

theorem counterClause1054 (q : Nat → Bool) : valuationOf q 890 = false ∨ valuationOf q 957 = false ∨ valuationOf q 977 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (890)) (literal (valuationOf q) (957)) (literal (valuationOf q) (977)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 4 8 (meaning890 q) (meaning957 q) (meaning977 q) hs
  change valuationOf q 890 = false ∨ valuationOf q 957 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1054 (q : Snake 81) (h : Conditions q) : valuation q 890 = false ∨ valuation q 957 = false ∨ valuation q 977 = true := counterClause1054 (baseVal q)

theorem counterClause1055 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 951 = false ∨ valuationOf q 972 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (951)) (literal (valuationOf q) (972)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 5 2 (meaning891 q) (meaning951 q) (meaning972 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 951 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1055 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 951 = false ∨ valuation q 972 = true := counterClause1055 (baseVal q)

theorem counterClause1056 (q : Nat → Bool) : valuationOf q 891 = false ∨ valuationOf q 952 = false ∨ valuationOf q 973 = true := by
  have hs : count966 q = (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) + (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (l₂ := [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61])
  have hm := merge_two (literal (valuationOf q) (891)) (literal (valuationOf q) (952)) (literal (valuationOf q) (973)) (countLit q [-1, -3, -4, -5, -8, -11, -12, -14, -18, -20, -21, -23, -24, -27, -29]) (countLit q [-32, -35, -37, -38, -39, -43, -45, -46, -47, -51, -52, -53, -55, -57, -60, -61]) (count966 q) 5 3 (meaning891 q) (meaning952 q) (meaning973 q) hs
  change valuationOf q 891 = false ∨ valuationOf q 952 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1056 (q : Snake 81) (h : Conditions q) : valuation q 891 = false ∨ valuation q 952 = false ∨ valuation q 973 = true := counterClause1056 (baseVal q)

theorem block32 (q : Snake 81) (h : Conditions q) : B112E153.Block32 (valuation q) :=
  ⟨clause1025 q h, clause1026 q h, clause1027 q h, clause1028 q h, clause1029 q h, clause1030 q h, clause1031 q h, clause1032 q h, clause1033 q h, clause1034 q h, clause1035 q h, clause1036 q h, clause1037 q h, clause1038 q h, clause1039 q h, clause1040 q h, clause1041 q h, clause1042 q h, clause1043 q h, clause1044 q h, clause1045 q h, clause1046 q h, clause1047 q h, clause1048 q h, clause1049 q h, clause1050 q h, clause1051 q h, clause1052 q h, clause1053 q h, clause1054 q h, clause1055 q h, clause1056 q h⟩

end
end Snake9.Regrowth.E112153
