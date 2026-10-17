import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 960 = false ∨ valuationOf q 981 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (960)) (literal (valuationOf q) (981)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 6 9 (meaning898 q) (meaning960 q) (meaning981 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 960 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 960 = false ∨ valuation q 981 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 961 = false ∨ valuationOf q 982 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (961)) (literal (valuationOf q) (982)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 6 10 (meaning898 q) (meaning961 q) (meaning982 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 961 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 961 = false ∨ valuation q 982 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 952 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (952)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 7 1 (meaning899 q) (meaning952 q) (meaning974 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 952 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 952 = false ∨ valuation q 974 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 953 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (953)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 7 2 (meaning899 q) (meaning953 q) (meaning975 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 953 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 953 = false ∨ valuation q 975 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 954 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (954)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 7 3 (meaning899 q) (meaning954 q) (meaning976 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 954 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 954 = false ∨ valuation q 976 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 955 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (955)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 7 4 (meaning899 q) (meaning955 q) (meaning977 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 955 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 955 = false ∨ valuation q 977 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 956 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (956)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 7 5 (meaning899 q) (meaning956 q) (meaning978 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 956 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 956 = false ∨ valuation q 978 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 957 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (957)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 7 6 (meaning899 q) (meaning957 q) (meaning979 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 957 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 957 = false ∨ valuation q 979 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 958 = false ∨ valuationOf q 980 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (958)) (literal (valuationOf q) (980)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 7 7 (meaning899 q) (meaning958 q) (meaning980 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 958 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 958 = false ∨ valuation q 980 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 959 = false ∨ valuationOf q 981 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (959)) (literal (valuationOf q) (981)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 7 8 (meaning899 q) (meaning959 q) (meaning981 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 959 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 959 = false ∨ valuation q 981 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 952 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (952)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 8 1 (meaning900 q) (meaning952 q) (meaning975 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 952 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 952 = false ∨ valuation q 975 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 953 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (953)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 8 2 (meaning900 q) (meaning953 q) (meaning976 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 953 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 953 = false ∨ valuation q 976 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 954 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (954)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 8 3 (meaning900 q) (meaning954 q) (meaning977 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 954 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 954 = false ∨ valuation q 977 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 955 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (955)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 8 4 (meaning900 q) (meaning955 q) (meaning978 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 955 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 955 = false ∨ valuation q 978 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 956 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (956)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 8 5 (meaning900 q) (meaning956 q) (meaning979 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 956 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 956 = false ∨ valuation q 979 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 957 = false ∨ valuationOf q 980 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (957)) (literal (valuationOf q) (980)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 8 6 (meaning900 q) (meaning957 q) (meaning980 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 957 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 957 = false ∨ valuation q 980 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 958 = false ∨ valuationOf q 981 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (958)) (literal (valuationOf q) (981)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 8 7 (meaning900 q) (meaning958 q) (meaning981 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 958 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 958 = false ∨ valuation q 981 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 952 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (901)) (literal (valuationOf q) (952)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 9 1 (meaning901 q) (meaning952 q) (meaning976 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 952 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 952 = false ∨ valuation q 976 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 953 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (901)) (literal (valuationOf q) (953)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 9 2 (meaning901 q) (meaning953 q) (meaning977 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 953 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 953 = false ∨ valuation q 977 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 954 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (901)) (literal (valuationOf q) (954)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 9 3 (meaning901 q) (meaning954 q) (meaning978 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 954 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 954 = false ∨ valuation q 978 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 955 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (901)) (literal (valuationOf q) (955)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 9 4 (meaning901 q) (meaning955 q) (meaning979 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 955 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 955 = false ∨ valuation q 979 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 956 = false ∨ valuationOf q 980 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (901)) (literal (valuationOf q) (956)) (literal (valuationOf q) (980)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 9 5 (meaning901 q) (meaning956 q) (meaning980 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 956 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 956 = false ∨ valuation q 980 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 957 = false ∨ valuationOf q 981 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (901)) (literal (valuationOf q) (957)) (literal (valuationOf q) (981)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 9 6 (meaning901 q) (meaning957 q) (meaning981 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 957 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 957 = false ∨ valuation q 981 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 953 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (902)) (literal (valuationOf q) (953)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 10 2 (meaning902 q) (meaning953 q) (meaning978 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 953 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 953 = false ∨ valuation q 978 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 954 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (902)) (literal (valuationOf q) (954)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 10 3 (meaning902 q) (meaning954 q) (meaning979 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 954 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 954 = false ∨ valuation q 979 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 955 = false ∨ valuationOf q 980 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (902)) (literal (valuationOf q) (955)) (literal (valuationOf q) (980)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 10 4 (meaning902 q) (meaning955 q) (meaning980 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 955 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 955 = false ∨ valuation q 980 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-63]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65])
  have hm := merge_right (literal (valuationOf q) (-65)) (literal (valuationOf q) (988)) (countLit q [-63]) (countLit q [-65]) (count988 q) 1 (meaningNeg65 q) (meaning988 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 988 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-63]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (988)) (countLit q [-63]) (countLit q [-65]) (count988 q) 1 (meaningNeg63 q) (meaning988 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 988 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 65 = true ∨ valuationOf q 989 = true := by
  have hs : count988 q = (countLit q [-63]) + (countLit q [-65]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-65])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-65)) (literal (valuationOf q) (989)) (countLit q [-63]) (countLit q [-65]) (count988 q) 1 1 (meaningNeg63 q) (meaningNeg65 q) (meaning989 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 65)) = false ∨ valuationOf q 989 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 65 = true ∨ valuation q 989 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-62]) + (countLit q [-63, -65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -65])
  have hm := merge_right (literal (valuationOf q) (988)) (literal (valuationOf q) (990)) (countLit q [-62]) (countLit q [-63, -65]) (count990 q) 1 (meaning988 q) (meaning990 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 990 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-62]) + (countLit q [-63, -65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -65])
  have hm := merge_right (literal (valuationOf q) (989)) (literal (valuationOf q) (991)) (countLit q [-62]) (countLit q [-63, -65]) (count990 q) 2 (meaning989 q) (meaning991 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 991 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 62 = true ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-62]) + (countLit q [-63, -65]) := List.countP_append (p := literal q) (l₁ := [-62]) (l₂ := [-63, -65])
  have hm := merge_left (literal (valuationOf q) (-62)) (literal (valuationOf q) (990)) (countLit q [-62]) (countLit q [-63, -65]) (count990 q) 1 (meaningNeg62 q) (meaning990 q) hs
  change (! (valuationOf q 62)) = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 62 = true ∨ valuation q 990 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E256.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112256
