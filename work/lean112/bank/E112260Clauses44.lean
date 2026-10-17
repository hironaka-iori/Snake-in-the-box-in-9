import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 958 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (893)) (literal (valuationOf q) (958)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 1 7 (meaning893 q) (meaning958 q) (meaning974 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 958 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 958 = false ∨ valuation q 974 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 959 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (893)) (literal (valuationOf q) (959)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 1 8 (meaning893 q) (meaning959 q) (meaning975 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 959 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 959 = false ∨ valuation q 975 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 956 = false ∨ valuationOf q 973 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (956)) (literal (valuationOf q) (973)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 2 5 (meaning894 q) (meaning956 q) (meaning973 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 956 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 956 = false ∨ valuation q 973 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 957 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (957)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 2 6 (meaning894 q) (meaning957 q) (meaning974 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 957 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 957 = false ∨ valuation q 974 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 958 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (958)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 2 7 (meaning894 q) (meaning958 q) (meaning975 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 958 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 958 = false ∨ valuation q 975 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 959 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (959)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 2 8 (meaning894 q) (meaning959 q) (meaning976 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 959 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 959 = false ∨ valuation q 976 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 960 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (960)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 2 9 (meaning894 q) (meaning960 q) (meaning977 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 960 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 960 = false ∨ valuation q 977 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 954 = false ∨ valuationOf q 972 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (954)) (literal (valuationOf q) (972)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 3 3 (meaning895 q) (meaning954 q) (meaning972 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 954 = false ∨ valuationOf q 972 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 954 = false ∨ valuation q 972 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 955 = false ∨ valuationOf q 973 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (955)) (literal (valuationOf q) (973)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 3 4 (meaning895 q) (meaning955 q) (meaning973 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 955 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 955 = false ∨ valuation q 973 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 956 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (956)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 3 5 (meaning895 q) (meaning956 q) (meaning974 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 956 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 956 = false ∨ valuation q 974 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 957 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (957)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 3 6 (meaning895 q) (meaning957 q) (meaning975 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 957 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 957 = false ∨ valuation q 975 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 958 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (958)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 3 7 (meaning895 q) (meaning958 q) (meaning976 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 958 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 958 = false ∨ valuation q 976 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 959 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (959)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 3 8 (meaning895 q) (meaning959 q) (meaning977 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 959 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 959 = false ∨ valuation q 977 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 895 = false ∨ valuationOf q 960 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (895)) (literal (valuationOf q) (960)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 3 9 (meaning895 q) (meaning960 q) (meaning978 q) hs
  change valuationOf q 895 = false ∨ valuationOf q 960 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 895 = false ∨ valuation q 960 = false ∨ valuation q 978 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 954 = false ∨ valuationOf q 973 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (954)) (literal (valuationOf q) (973)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 4 3 (meaning896 q) (meaning954 q) (meaning973 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 954 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 954 = false ∨ valuation q 973 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 955 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (955)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 4 4 (meaning896 q) (meaning955 q) (meaning974 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 955 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 955 = false ∨ valuation q 974 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 956 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (956)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 4 5 (meaning896 q) (meaning956 q) (meaning975 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 956 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 956 = false ∨ valuation q 975 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 957 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (957)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 4 6 (meaning896 q) (meaning957 q) (meaning976 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 957 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 957 = false ∨ valuation q 976 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 958 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (958)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 4 7 (meaning896 q) (meaning958 q) (meaning977 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 958 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 958 = false ∨ valuation q 977 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 959 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (959)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 4 8 (meaning896 q) (meaning959 q) (meaning978 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 959 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 959 = false ∨ valuation q 978 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 896 = false ∨ valuationOf q 960 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (896)) (literal (valuationOf q) (960)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 4 9 (meaning896 q) (meaning960 q) (meaning979 q) hs
  change valuationOf q 896 = false ∨ valuationOf q 960 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 896 = false ∨ valuation q 960 = false ∨ valuation q 979 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 953 = false ∨ valuationOf q 973 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (953)) (literal (valuationOf q) (973)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 5 2 (meaning897 q) (meaning953 q) (meaning973 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 953 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 953 = false ∨ valuation q 973 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 954 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (954)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 5 3 (meaning897 q) (meaning954 q) (meaning974 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 954 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 954 = false ∨ valuation q 974 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 955 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (955)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 5 4 (meaning897 q) (meaning955 q) (meaning975 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 955 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 955 = false ∨ valuation q 975 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 956 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (956)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 5 5 (meaning897 q) (meaning956 q) (meaning976 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 956 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 956 = false ∨ valuation q 976 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 957 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (957)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 5 6 (meaning897 q) (meaning957 q) (meaning977 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 957 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 957 = false ∨ valuation q 977 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 958 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (958)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 5 7 (meaning897 q) (meaning958 q) (meaning978 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 958 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 958 = false ∨ valuation q 978 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 897 = false ∨ valuationOf q 959 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (897)) (literal (valuationOf q) (959)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 5 8 (meaning897 q) (meaning959 q) (meaning979 q) hs
  change valuationOf q 897 = false ∨ valuationOf q 959 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 897 = false ∨ valuation q 959 = false ∨ valuation q 979 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 953 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (953)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 6 2 (meaning898 q) (meaning953 q) (meaning974 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 953 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 953 = false ∨ valuation q 974 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 954 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (954)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 6 3 (meaning898 q) (meaning954 q) (meaning975 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 954 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 954 = false ∨ valuation q 975 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 955 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (955)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 6 4 (meaning898 q) (meaning955 q) (meaning976 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 955 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 955 = false ∨ valuation q 976 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 956 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (956)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 6 5 (meaning898 q) (meaning956 q) (meaning977 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 956 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 956 = false ∨ valuation q 977 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E260.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112260
