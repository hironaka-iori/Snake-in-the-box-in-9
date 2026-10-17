import E112097Semantics
import B112E097Inputs
namespace Snake9.Regrowth.E112097
noncomputable section
local instance blockDec35 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1121 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 939 = false ∨ valuationOf q 960 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (939)) (literal (valuationOf q) (960)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 6 4 (meaning882 q) (meaning939 q) (meaning960 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 939 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1121 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 939 = false ∨ valuation q 960 = true := counterClause1121 (baseVal q)

theorem counterClause1122 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 940 = false ∨ valuationOf q 961 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (940)) (literal (valuationOf q) (961)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 6 5 (meaning882 q) (meaning940 q) (meaning961 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 940 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1122 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 940 = false ∨ valuation q 961 = true := counterClause1122 (baseVal q)

theorem counterClause1123 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 941 = false ∨ valuationOf q 962 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (941)) (literal (valuationOf q) (962)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 6 6 (meaning882 q) (meaning941 q) (meaning962 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 941 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1123 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 941 = false ∨ valuation q 962 = true := counterClause1123 (baseVal q)

theorem counterClause1124 (q : Nat → Bool) : valuationOf q 882 = false ∨ valuationOf q 942 = false ∨ valuationOf q 963 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (882)) (literal (valuationOf q) (942)) (literal (valuationOf q) (963)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 6 7 (meaning882 q) (meaning942 q) (meaning963 q) hs
  change valuationOf q 882 = false ∨ valuationOf q 942 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1124 (q : Snake 81) (h : Conditions q) : valuation q 882 = false ∨ valuation q 942 = false ∨ valuation q 963 = true := counterClause1124 (baseVal q)

theorem counterClause1125 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 938 = false ∨ valuationOf q 960 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (938)) (literal (valuationOf q) (960)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 7 3 (meaning883 q) (meaning938 q) (meaning960 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 938 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1125 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 938 = false ∨ valuation q 960 = true := counterClause1125 (baseVal q)

theorem counterClause1126 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 939 = false ∨ valuationOf q 961 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (939)) (literal (valuationOf q) (961)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 7 4 (meaning883 q) (meaning939 q) (meaning961 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 939 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1126 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 939 = false ∨ valuation q 961 = true := counterClause1126 (baseVal q)

theorem counterClause1127 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 940 = false ∨ valuationOf q 962 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (940)) (literal (valuationOf q) (962)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 7 5 (meaning883 q) (meaning940 q) (meaning962 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 940 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1127 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 940 = false ∨ valuation q 962 = true := counterClause1127 (baseVal q)

theorem counterClause1128 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 941 = false ∨ valuationOf q 963 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (941)) (literal (valuationOf q) (963)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 7 6 (meaning883 q) (meaning941 q) (meaning963 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 941 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1128 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 941 = false ∨ valuation q 963 = true := counterClause1128 (baseVal q)

theorem counterClause1129 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 942 = false ∨ valuationOf q 964 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (942)) (literal (valuationOf q) (964)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 7 7 (meaning883 q) (meaning942 q) (meaning964 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 942 = false ∨ valuationOf q 964 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1129 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 942 = false ∨ valuation q 964 = true := counterClause1129 (baseVal q)

theorem counterClause1130 (q : Nat → Bool) : valuationOf q 883 = false ∨ valuationOf q 943 = false ∨ valuationOf q 965 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (883)) (literal (valuationOf q) (943)) (literal (valuationOf q) (965)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 7 8 (meaning883 q) (meaning943 q) (meaning965 q) hs
  change valuationOf q 883 = false ∨ valuationOf q 943 = false ∨ valuationOf q 965 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1130 (q : Snake 81) (h : Conditions q) : valuation q 883 = false ∨ valuation q 943 = false ∨ valuation q 965 = true := counterClause1130 (baseVal q)

theorem counterClause1131 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 938 = false ∨ valuationOf q 961 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (938)) (literal (valuationOf q) (961)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 8 3 (meaning884 q) (meaning938 q) (meaning961 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 938 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1131 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 938 = false ∨ valuation q 961 = true := counterClause1131 (baseVal q)

theorem counterClause1132 (q : Nat → Bool) : valuationOf q 884 = false ∨ valuationOf q 940 = false ∨ valuationOf q 963 = true := by
  have hs : count951 q = (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) + (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (l₂ := [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59])
  have hm := merge_two (literal (valuationOf q) (884)) (literal (valuationOf q) (940)) (literal (valuationOf q) (963)) (countLit q [-1, -3, -4, -6, -7, -8, -10, -13, -18, -20, -21, -22, -25, -28, -29]) (countLit q [-33, -34, -36, -38, -40, -43, -44, -46, -47, -50, -53, -54, -55, -57, -59]) (count951 q) 8 5 (meaning884 q) (meaning940 q) (meaning963 q) hs
  change valuationOf q 884 = false ∨ valuationOf q 940 = false ∨ valuationOf q 963 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1132 (q : Snake 81) (h : Conditions q) : valuation q 884 = false ∨ valuation q 940 = false ∨ valuation q 963 = true := counterClause1132 (baseVal q)

theorem counterClause1133 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 972 = true := by
  have hs : count972 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_right (literal (valuationOf q) (-65)) (literal (valuationOf q) (972)) (countLit q [-64]) (countLit q [-65]) (count972 q) 1 (meaningNeg65 q) (meaning972 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1133 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 972 = true := counterClause1133 (baseVal q)

theorem counterClause1134 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 972 = true := by
  have hs : count972 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-64)) (literal (valuationOf q) (972)) (countLit q [-64]) (countLit q [-65]) (count972 q) 1 (meaningNeg64 q) (meaning972 q) hs
  change (! (valuationOf q 64)) = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1134 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 972 = true := counterClause1134 (baseVal q)

theorem counterClause1135 (q : Nat → Bool) : valuationOf q 64 = true ∨ valuationOf q 65 = true ∨ valuationOf q 973 = true := by
  have hs : count972 q = (countLit q [-64]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-64]) (l₂ := [-65])
  have hm := merge_two (literal (valuationOf q) (-64)) (literal (valuationOf q) (-65)) (literal (valuationOf q) (973)) (countLit q [-64]) (countLit q [-65]) (count972 q) 1 1 (meaningNeg64 q) (meaningNeg65 q) (meaning973 q) hs
  change (! (valuationOf q 64)) = false ∨ (! (valuationOf q 65)) = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1135 (q : Snake 81) (h : Conditions q) : valuation q 64 = true ∨ valuation q 65 = true ∨ valuation q 973 = true := counterClause1135 (baseVal q)

theorem counterClause1136 (q : Nat → Bool) : valuationOf q 972 = false ∨ valuationOf q 974 = true := by
  have hs : count974 q = (countLit q [-61]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64, -65])
  have hm := merge_right (literal (valuationOf q) (972)) (literal (valuationOf q) (974)) (countLit q [-61]) (countLit q [-64, -65]) (count974 q) 1 (meaning972 q) (meaning974 q) hs
  change valuationOf q 972 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1136 (q : Snake 81) (h : Conditions q) : valuation q 972 = false ∨ valuation q 974 = true := counterClause1136 (baseVal q)

theorem counterClause1137 (q : Nat → Bool) : valuationOf q 973 = false ∨ valuationOf q 975 = true := by
  have hs : count974 q = (countLit q [-61]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64, -65])
  have hm := merge_right (literal (valuationOf q) (973)) (literal (valuationOf q) (975)) (countLit q [-61]) (countLit q [-64, -65]) (count974 q) 2 (meaning973 q) (meaning975 q) hs
  change valuationOf q 973 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1137 (q : Snake 81) (h : Conditions q) : valuation q 973 = false ∨ valuation q 975 = true := counterClause1137 (baseVal q)

theorem counterClause1138 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 974 = true := by
  have hs : count974 q = (countLit q [-61]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64, -65])
  have hm := merge_left (literal (valuationOf q) (-61)) (literal (valuationOf q) (974)) (countLit q [-61]) (countLit q [-64, -65]) (count974 q) 1 (meaningNeg61 q) (meaning974 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1138 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 974 = true := counterClause1138 (baseVal q)

theorem counterClause1139 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 972 = false ∨ valuationOf q 975 = true := by
  have hs : count974 q = (countLit q [-61]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64, -65])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (972)) (literal (valuationOf q) (975)) (countLit q [-61]) (countLit q [-64, -65]) (count974 q) 1 1 (meaningNeg61 q) (meaning972 q) (meaning975 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 972 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1139 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 972 = false ∨ valuation q 975 = true := counterClause1139 (baseVal q)

theorem counterClause1140 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 973 = false ∨ valuationOf q 976 = true := by
  have hs : count974 q = (countLit q [-61]) + (countLit q [-64, -65]) := List.countP_append (p := literal q) (l₁ := [-61]) (l₂ := [-64, -65])
  have hm := merge_two (literal (valuationOf q) (-61)) (literal (valuationOf q) (973)) (literal (valuationOf q) (976)) (countLit q [-61]) (countLit q [-64, -65]) (count974 q) 1 2 (meaningNeg61 q) (meaning973 q) (meaning976 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 973 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1140 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 973 = false ∨ valuation q 976 = true := counterClause1140 (baseVal q)

theorem counterClause1141 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 977 = true := by
  have hs : count977 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (977)) (countLit q [-69]) (countLit q [-70]) (count977 q) 1 (meaningNeg70 q) (meaning977 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1141 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 977 = true := counterClause1141 (baseVal q)

theorem counterClause1142 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 977 = true := by
  have hs : count977 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (977)) (countLit q [-69]) (countLit q [-70]) (count977 q) 1 (meaningNeg69 q) (meaning977 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1142 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 977 = true := counterClause1142 (baseVal q)

theorem counterClause1143 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 70 = true ∨ valuationOf q 978 = true := by
  have hs : count977 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-70)) (literal (valuationOf q) (978)) (countLit q [-69]) (countLit q [-70]) (count977 q) 1 1 (meaningNeg69 q) (meaningNeg70 q) (meaning978 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 70)) = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1143 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 70 = true ∨ valuation q 978 = true := counterClause1143 (baseVal q)

theorem counterClause1144 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 979 = true := by
  have hs : count979 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (979)) (countLit q [-72]) (countLit q [-74]) (count979 q) 1 (meaningNeg74 q) (meaning979 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1144 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 979 = true := counterClause1144 (baseVal q)

theorem counterClause1145 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 979 = true := by
  have hs : count979 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (979)) (countLit q [-72]) (countLit q [-74]) (count979 q) 1 (meaningNeg72 q) (meaning979 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1145 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 979 = true := counterClause1145 (baseVal q)

theorem counterClause1146 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 74 = true ∨ valuationOf q 980 = true := by
  have hs : count979 q = (countLit q [-72]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-74])
  have hm := merge_two (literal (valuationOf q) (-72)) (literal (valuationOf q) (-74)) (literal (valuationOf q) (980)) (countLit q [-72]) (countLit q [-74]) (count979 q) 1 1 (meaningNeg72 q) (meaningNeg74 q) (meaning980 q) hs
  change (! (valuationOf q 72)) = false ∨ (! (valuationOf q 74)) = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1146 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 74 = true ∨ valuation q 980 = true := counterClause1146 (baseVal q)

theorem counterClause1147 (q : Nat → Bool) : valuationOf q 979 = false ∨ valuationOf q 981 = true := by
  have hs : count981 q = (countLit q [-69, -70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (979)) (literal (valuationOf q) (981)) (countLit q [-69, -70]) (countLit q [-72, -74]) (count981 q) 1 (meaning979 q) (meaning981 q) hs
  change valuationOf q 979 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1147 (q : Snake 81) (h : Conditions q) : valuation q 979 = false ∨ valuation q 981 = true := counterClause1147 (baseVal q)

theorem counterClause1148 (q : Nat → Bool) : valuationOf q 980 = false ∨ valuationOf q 982 = true := by
  have hs : count981 q = (countLit q [-69, -70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -74])
  have hm := merge_right (literal (valuationOf q) (980)) (literal (valuationOf q) (982)) (countLit q [-69, -70]) (countLit q [-72, -74]) (count981 q) 2 (meaning980 q) (meaning982 q) hs
  change valuationOf q 980 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1148 (q : Snake 81) (h : Conditions q) : valuation q 980 = false ∨ valuation q 982 = true := counterClause1148 (baseVal q)

theorem counterClause1149 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 981 = true := by
  have hs : count981 q = (countLit q [-69, -70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -74])
  have hm := merge_left (literal (valuationOf q) (977)) (literal (valuationOf q) (981)) (countLit q [-69, -70]) (countLit q [-72, -74]) (count981 q) 1 (meaning977 q) (meaning981 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1149 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 981 = true := counterClause1149 (baseVal q)

theorem counterClause1150 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 979 = false ∨ valuationOf q 982 = true := by
  have hs : count981 q = (countLit q [-69, -70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (979)) (literal (valuationOf q) (982)) (countLit q [-69, -70]) (countLit q [-72, -74]) (count981 q) 1 1 (meaning977 q) (meaning979 q) (meaning982 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 979 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1150 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 979 = false ∨ valuation q 982 = true := counterClause1150 (baseVal q)

theorem counterClause1151 (q : Nat → Bool) : valuationOf q 977 = false ∨ valuationOf q 980 = false ∨ valuationOf q 983 = true := by
  have hs : count981 q = (countLit q [-69, -70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -74])
  have hm := merge_two (literal (valuationOf q) (977)) (literal (valuationOf q) (980)) (literal (valuationOf q) (983)) (countLit q [-69, -70]) (countLit q [-72, -74]) (count981 q) 1 2 (meaning977 q) (meaning980 q) (meaning983 q) hs
  change valuationOf q 977 = false ∨ valuationOf q 980 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1151 (q : Snake 81) (h : Conditions q) : valuation q 977 = false ∨ valuation q 980 = false ∨ valuation q 983 = true := counterClause1151 (baseVal q)

theorem counterClause1152 (q : Nat → Bool) : valuationOf q 978 = false ∨ valuationOf q 982 = true := by
  have hs : count981 q = (countLit q [-69, -70]) + (countLit q [-72, -74]) := List.countP_append (p := literal q) (l₁ := [-69, -70]) (l₂ := [-72, -74])
  have hm := merge_left (literal (valuationOf q) (978)) (literal (valuationOf q) (982)) (countLit q [-69, -70]) (countLit q [-72, -74]) (count981 q) 2 (meaning978 q) (meaning982 q) hs
  change valuationOf q 978 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1152 (q : Snake 81) (h : Conditions q) : valuation q 978 = false ∨ valuation q 982 = true := counterClause1152 (baseVal q)

theorem block35 (q : Snake 81) (h : Conditions q) : B112E097.Block35 (valuation q) :=
  ⟨clause1121 q h, clause1122 q h, clause1123 q h, clause1124 q h, clause1125 q h, clause1126 q h, clause1127 q h, clause1128 q h, clause1129 q h, clause1130 q h, clause1131 q h, clause1132 q h, clause1133 q h, clause1134 q h, clause1135 q h, clause1136 q h, clause1137 q h, clause1138 q h, clause1139 q h, clause1140 q h, clause1141 q h, clause1142 q h, clause1143 q h, clause1144 q h, clause1145 q h, clause1146 q h, clause1147 q h, clause1148 q h, clause1149 q h, clause1150 q h, clause1151 q h, clause1152 q h⟩

end
end Snake9.Regrowth.E112097
