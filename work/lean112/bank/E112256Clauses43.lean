import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 961 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (961)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 2 10 (meaning894 q) (meaning961 q) (meaning978 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 961 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 961 = false ∨ valuation q 978 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 955 = false ∨ valuationOf q 973 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (955)) (literal (valuationOf q) (973)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 3 4 (meaning895 q) (meaning955 q) (meaning973 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 955 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 955 = false ∨ valuation q 973 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 956 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (956)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 3 5 (meaning895 q) (meaning956 q) (meaning974 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 956 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 956 = false ∨ valuation q 974 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 957 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (957)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 3 6 (meaning895 q) (meaning957 q) (meaning975 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 957 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 957 = false ∨ valuation q 975 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 958 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (958)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 3 7 (meaning895 q) (meaning958 q) (meaning976 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 958 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 958 = false ∨ valuation q 976 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 959 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (959)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 3 8 (meaning895 q) (meaning959 q) (meaning977 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 959 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 959 = false ∨ valuation q 977 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 960 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (960)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 3 9 (meaning895 q) (meaning960 q) (meaning978 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 960 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 960 = false ∨ valuation q 978 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 961 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (961)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 3 10 (meaning895 q) (meaning961 q) (meaning979 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 961 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 961 = false ∨ valuation q 979 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 954 = false ∨ valuationOf q 973 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (954)) (literal (valuationOf q) (973)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 4 3 (meaning896 q) (meaning954 q) (meaning973 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 954 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 954 = false ∨ valuation q 973 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 955 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (955)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 4 4 (meaning896 q) (meaning955 q) (meaning974 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 955 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 955 = false ∨ valuation q 974 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 956 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (956)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 4 5 (meaning896 q) (meaning956 q) (meaning975 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 956 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 956 = false ∨ valuation q 975 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 957 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (957)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 4 6 (meaning896 q) (meaning957 q) (meaning976 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 957 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 957 = false ∨ valuation q 976 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 958 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (958)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 4 7 (meaning896 q) (meaning958 q) (meaning977 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 958 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 958 = false ∨ valuation q 977 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 959 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (959)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 4 8 (meaning896 q) (meaning959 q) (meaning978 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 959 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 959 = false ∨ valuation q 978 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 960 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (960)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 4 9 (meaning896 q) (meaning960 q) (meaning979 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 960 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 960 = false ∨ valuation q 979 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 961 = false ∨ valuationOf q 980 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (961)) (literal (valuationOf q) (980)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 4 10 (meaning896 q) (meaning961 q) (meaning980 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 961 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 961 = false ∨ valuation q 980 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 962 = false ∨ valuationOf q 981 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (962)) (literal (valuationOf q) (981)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 4 11 (meaning896 q) (meaning962 q) (meaning981 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 962 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 962 = false ∨ valuation q 981 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 954 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (954)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 5 3 (meaning897 q) (meaning954 q) (meaning974 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 954 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 954 = false ∨ valuation q 974 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 955 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (955)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 5 4 (meaning897 q) (meaning955 q) (meaning975 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 955 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 955 = false ∨ valuation q 975 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 956 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (956)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 5 5 (meaning897 q) (meaning956 q) (meaning976 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 956 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 956 = false ∨ valuation q 976 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 957 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (957)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 5 6 (meaning897 q) (meaning957 q) (meaning977 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 957 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 957 = false ∨ valuation q 977 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 958 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (958)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 5 7 (meaning897 q) (meaning958 q) (meaning978 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 958 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 958 = false ∨ valuation q 978 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 959 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (959)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 5 8 (meaning897 q) (meaning959 q) (meaning979 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 959 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 959 = false ∨ valuation q 979 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 960 = false ∨ valuationOf q 980 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (960)) (literal (valuationOf q) (980)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 5 9 (meaning897 q) (meaning960 q) (meaning980 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 960 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 960 = false ∨ valuation q 980 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 961 = false ∨ valuationOf q 981 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (961)) (literal (valuationOf q) (981)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 5 10 (meaning897 q) (meaning961 q) (meaning981 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 961 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 961 = false ∨ valuation q 981 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 953 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (953)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 6 2 (meaning898 q) (meaning953 q) (meaning974 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 953 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 953 = false ∨ valuation q 974 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 954 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (954)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 6 3 (meaning898 q) (meaning954 q) (meaning975 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 954 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 954 = false ∨ valuation q 975 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 955 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (955)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 6 4 (meaning898 q) (meaning955 q) (meaning976 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 955 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 955 = false ∨ valuation q 976 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 956 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (956)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 6 5 (meaning898 q) (meaning956 q) (meaning977 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 956 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 956 = false ∨ valuation q 977 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 957 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (957)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 6 6 (meaning898 q) (meaning957 q) (meaning978 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 957 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 957 = false ∨ valuation q 978 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 958 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (958)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 6 7 (meaning898 q) (meaning958 q) (meaning979 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 958 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 958 = false ∨ valuation q 979 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 959 = false ∨ valuationOf q 980 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (959)) (literal (valuationOf q) (980)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 6 8 (meaning898 q) (meaning959 q) (meaning980 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 959 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 959 = false ∨ valuation q 980 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E256.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112256
