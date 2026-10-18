import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec45 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1441 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 957 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (957)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 6 6 (meaning898 q) (meaning957 q) (meaning978 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 957 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1441 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 957 = false ∨ valuation q 978 = true := counterClause1441 (baseVal q)

theorem counterClause1442 (q : Nat → Bool) : valuationOf q 898 = false ∨ valuationOf q 958 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (898)) (literal (valuationOf q) (958)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 6 7 (meaning898 q) (meaning958 q) (meaning979 q) hs
  change valuationOf q 898 = false ∨ valuationOf q 958 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1442 (q : Snake 81) (h : Conditions q) : valuation q 898 = false ∨ valuation q 958 = false ∨ valuation q 979 = true := counterClause1442 (baseVal q)

theorem counterClause1443 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 952 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (952)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 7 1 (meaning899 q) (meaning952 q) (meaning974 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 952 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1443 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 952 = false ∨ valuation q 974 = true := counterClause1443 (baseVal q)

theorem counterClause1444 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 953 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (953)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 7 2 (meaning899 q) (meaning953 q) (meaning975 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 953 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1444 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 953 = false ∨ valuation q 975 = true := counterClause1444 (baseVal q)

theorem counterClause1445 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 954 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (954)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 7 3 (meaning899 q) (meaning954 q) (meaning976 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 954 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1445 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 954 = false ∨ valuation q 976 = true := counterClause1445 (baseVal q)

theorem counterClause1446 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 955 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (955)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 7 4 (meaning899 q) (meaning955 q) (meaning977 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 955 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1446 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 955 = false ∨ valuation q 977 = true := counterClause1446 (baseVal q)

theorem counterClause1447 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 956 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (956)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 7 5 (meaning899 q) (meaning956 q) (meaning978 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 956 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1447 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 956 = false ∨ valuation q 978 = true := counterClause1447 (baseVal q)

theorem counterClause1448 (q : Nat → Bool) : valuationOf q 899 = false ∨ valuationOf q 957 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (899)) (literal (valuationOf q) (957)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 7 6 (meaning899 q) (meaning957 q) (meaning979 q) hs
  change valuationOf q 899 = false ∨ valuationOf q 957 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1448 (q : Snake 81) (h : Conditions q) : valuation q 899 = false ∨ valuation q 957 = false ∨ valuation q 979 = true := counterClause1448 (baseVal q)

theorem counterClause1449 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 952 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (952)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 8 1 (meaning900 q) (meaning952 q) (meaning975 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 952 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1449 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 952 = false ∨ valuation q 975 = true := counterClause1449 (baseVal q)

theorem counterClause1450 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 953 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (953)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 8 2 (meaning900 q) (meaning953 q) (meaning976 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 953 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1450 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 953 = false ∨ valuation q 976 = true := counterClause1450 (baseVal q)

theorem counterClause1451 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 954 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (954)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 8 3 (meaning900 q) (meaning954 q) (meaning977 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 954 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1451 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 954 = false ∨ valuation q 977 = true := counterClause1451 (baseVal q)

theorem counterClause1452 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 955 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (955)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 8 4 (meaning900 q) (meaning955 q) (meaning978 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 955 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1452 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 955 = false ∨ valuation q 978 = true := counterClause1452 (baseVal q)

theorem counterClause1453 (q : Nat → Bool) : valuationOf q 900 = false ∨ valuationOf q 956 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (900)) (literal (valuationOf q) (956)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 8 5 (meaning900 q) (meaning956 q) (meaning979 q) hs
  change valuationOf q 900 = false ∨ valuationOf q 956 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1453 (q : Snake 81) (h : Conditions q) : valuation q 900 = false ∨ valuation q 956 = false ∨ valuation q 979 = true := counterClause1453 (baseVal q)

theorem counterClause1454 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 953 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (901)) (literal (valuationOf q) (953)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 9 2 (meaning901 q) (meaning953 q) (meaning977 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 953 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1454 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 953 = false ∨ valuation q 977 = true := counterClause1454 (baseVal q)

theorem counterClause1455 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 954 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (901)) (literal (valuationOf q) (954)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 9 3 (meaning901 q) (meaning954 q) (meaning978 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 954 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1455 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 954 = false ∨ valuation q 978 = true := counterClause1455 (baseVal q)

theorem counterClause1456 (q : Nat → Bool) : valuationOf q 901 = false ∨ valuationOf q 955 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (901)) (literal (valuationOf q) (955)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 9 4 (meaning901 q) (meaning955 q) (meaning979 q) hs
  change valuationOf q 901 = false ∨ valuationOf q 955 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1456 (q : Snake 81) (h : Conditions q) : valuation q 901 = false ∨ valuation q 955 = false ∨ valuation q 979 = true := counterClause1456 (baseVal q)

theorem counterClause1457 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 953 = false ∨ valuationOf q 978 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (902)) (literal (valuationOf q) (953)) (literal (valuationOf q) (978)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 10 2 (meaning902 q) (meaning953 q) (meaning978 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 953 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1457 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 953 = false ∨ valuation q 978 = true := counterClause1457 (baseVal q)

theorem counterClause1458 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 954 = false ∨ valuationOf q 979 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (902)) (literal (valuationOf q) (954)) (literal (valuationOf q) (979)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 10 3 (meaning902 q) (meaning954 q) (meaning979 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 954 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1458 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 954 = false ∨ valuation q 979 = true := counterClause1458 (baseVal q)

theorem counterClause1459 (q : Nat → Bool) : valuationOf q 902 = false ∨ valuationOf q 955 = false ∨ valuationOf q 980 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) + (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (l₂ := [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (902)) (literal (valuationOf q) (955)) (literal (valuationOf q) (980)) (countLit q [-1, -2, -5, -6, -7, -10, -12, -15, -16, -20, -21, -24, -26, -28, -30]) (countLit q [-32, -34, -36, -40, -42, -44, -46, -48, -49, -50, -51, -56, -60, -62, -64]) (count967 q) 10 4 (meaning902 q) (meaning955 q) (meaning980 q) hs
  change valuationOf q 902 = false ∨ valuationOf q 955 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1459 (q : Snake 81) (h : Conditions q) : valuation q 902 = false ∨ valuation q 955 = false ∨ valuation q 980 = true := counterClause1459 (baseVal q)

theorem counterClause1460 (q : Nat → Bool) : valuationOf q 68 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_right (literal (valuationOf q) (-68)) (literal (valuationOf q) (988)) (countLit q [-67]) (countLit q [-68]) (count988 q) 1 (meaningNeg68 q) (meaning988 q) hs
  change (! (valuationOf q 68)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1460 (q : Snake 81) (h : Conditions q) : valuation q 68 = true ∨ valuation q 988 = true := counterClause1460 (baseVal q)

theorem counterClause1461 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 988 = true := by
  have hs : count988 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (988)) (countLit q [-67]) (countLit q [-68]) (count988 q) 1 (meaningNeg67 q) (meaning988 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 988 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1461 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 988 = true := counterClause1461 (baseVal q)

theorem counterClause1462 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 68 = true ∨ valuationOf q 989 = true := by
  have hs : count988 q = (countLit q [-67]) + (countLit q [-68]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-68])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (-68)) (literal (valuationOf q) (989)) (countLit q [-67]) (countLit q [-68]) (count988 q) 1 1 (meaningNeg67 q) (meaningNeg68 q) (meaning989 q) hs
  change (! (valuationOf q 67)) = false ∨ (! (valuationOf q 68)) = false ∨ valuationOf q 989 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1462 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 68 = true ∨ valuation q 989 = true := counterClause1462 (baseVal q)

theorem counterClause1463 (q : Nat → Bool) : valuationOf q 988 = false ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-65]) + (countLit q [-67, -68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -68])
  have hm := merge_right (literal (valuationOf q) (988)) (literal (valuationOf q) (990)) (countLit q [-65]) (countLit q [-67, -68]) (count990 q) 1 (meaning988 q) (meaning990 q) hs
  change valuationOf q 988 = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1463 (q : Snake 81) (h : Conditions q) : valuation q 988 = false ∨ valuation q 990 = true := counterClause1463 (baseVal q)

theorem counterClause1464 (q : Nat → Bool) : valuationOf q 989 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-65]) + (countLit q [-67, -68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -68])
  have hm := merge_right (literal (valuationOf q) (989)) (literal (valuationOf q) (991)) (countLit q [-65]) (countLit q [-67, -68]) (count990 q) 2 (meaning989 q) (meaning991 q) hs
  change valuationOf q 989 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1464 (q : Snake 81) (h : Conditions q) : valuation q 989 = false ∨ valuation q 991 = true := counterClause1464 (baseVal q)

theorem counterClause1465 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 990 = true := by
  have hs : count990 q = (countLit q [-65]) + (countLit q [-67, -68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -68])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (990)) (countLit q [-65]) (countLit q [-67, -68]) (count990 q) 1 (meaningNeg65 q) (meaning990 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 990 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1465 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 990 = true := counterClause1465 (baseVal q)

theorem counterClause1466 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true := by
  have hs : count990 q = (countLit q [-65]) + (countLit q [-67, -68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -68])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (988)) (literal (valuationOf q) (991)) (countLit q [-65]) (countLit q [-67, -68]) (count990 q) 1 1 (meaningNeg65 q) (meaning988 q) (meaning991 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 988 = false ∨ valuationOf q 991 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1466 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 988 = false ∨ valuation q 991 = true := counterClause1466 (baseVal q)

theorem counterClause1467 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true := by
  have hs : count990 q = (countLit q [-65]) + (countLit q [-67, -68]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -68])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (989)) (literal (valuationOf q) (992)) (countLit q [-65]) (countLit q [-67, -68]) (count990 q) 1 2 (meaningNeg65 q) (meaning989 q) (meaning992 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 989 = false ∨ valuationOf q 992 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1467 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 989 = false ∨ valuation q 992 = true := counterClause1467 (baseVal q)

theorem counterClause1468 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 993 = true := by
  have hs : count993 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_right (literal (valuationOf q) (-72)) (literal (valuationOf q) (993)) (countLit q [-69]) (countLit q [-72]) (count993 q) 1 (meaningNeg72 q) (meaning993 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1468 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 993 = true := counterClause1468 (baseVal q)

theorem counterClause1469 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 993 = true := by
  have hs : count993 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (993)) (countLit q [-69]) (countLit q [-72]) (count993 q) 1 (meaningNeg69 q) (meaning993 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 993 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1469 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 993 = true := counterClause1469 (baseVal q)

theorem counterClause1470 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 72 = true ∨ valuationOf q 994 = true := by
  have hs : count993 q = (countLit q [-69]) + (countLit q [-72]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-72])
  have hm := merge_two (literal (valuationOf q) (-69)) (literal (valuationOf q) (-72)) (literal (valuationOf q) (994)) (countLit q [-69]) (countLit q [-72]) (count993 q) 1 1 (meaningNeg69 q) (meaningNeg72 q) (meaning994 q) hs
  change (! (valuationOf q 69)) = false ∨ (! (valuationOf q 72)) = false ∨ valuationOf q 994 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1470 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 72 = true ∨ valuation q 994 = true := counterClause1470 (baseVal q)

theorem counterClause1471 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_right (literal (valuationOf q) (-74)) (literal (valuationOf q) (995)) (countLit q [-73]) (countLit q [-74]) (count995 q) 1 (meaningNeg74 q) (meaning995 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1471 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 995 = true := counterClause1471 (baseVal q)

theorem counterClause1472 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 995 = true := by
  have hs : count995 q = (countLit q [-73]) + (countLit q [-74]) := List.countP_append (p := literal q) (l₁ := [-73]) (l₂ := [-74])
  have hm := merge_left (literal (valuationOf q) (-73)) (literal (valuationOf q) (995)) (countLit q [-73]) (countLit q [-74]) (count995 q) 1 (meaningNeg73 q) (meaning995 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 995 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1472 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 995 = true := counterClause1472 (baseVal q)

theorem block45 (q : Snake 81) (h : Conditions q) : B112E260.Block45 (valuation q) :=
  ⟨clause1441 q h, clause1442 q h, clause1443 q h, clause1444 q h, clause1445 q h, clause1446 q h, clause1447 q h, clause1448 q h, clause1449 q h, clause1450 q h, clause1451 q h, clause1452 q h, clause1453 q h, clause1454 q h, clause1455 q h, clause1456 q h, clause1457 q h, clause1458 q h, clause1459 q h, clause1460 q h, clause1461 q h, clause1462 q h, clause1463 q h, clause1464 q h, clause1465 q h, clause1466 q h, clause1467 q h, clause1468 q h, clause1469 q h, clause1470 q h, clause1471 q h, clause1472 q h⟩

end
end Snake9.Regrowth.E112260
