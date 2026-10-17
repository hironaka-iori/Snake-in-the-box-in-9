import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec46 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1473 (q : Nat → Bool) : valuationOf q 960 = false ∨ valuationOf q 970 = false ∨ valuationOf q 976 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (960)) (literal (valuationOf q) (970)) (literal (valuationOf q) (976)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 2 4 (meaning960 q) (meaning970 q) (meaning976 q) hs
  change valuationOf q 960 = false ∨ valuationOf q 970 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1473 (q : Snake 81) (h : Conditions q) : valuation q 960 = false ∨ valuation q 970 = false ∨ valuation q 976 = true := counterClause1473 (baseVal q)

theorem counterClause1474 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 967 = false ∨ valuationOf q 974 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (967)) (literal (valuationOf q) (974)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 3 1 (meaning961 q) (meaning967 q) (meaning974 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 967 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1474 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 967 = false ∨ valuation q 974 = true := counterClause1474 (baseVal q)

theorem counterClause1475 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 968 = false ∨ valuationOf q 975 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (968)) (literal (valuationOf q) (975)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 3 2 (meaning961 q) (meaning968 q) (meaning975 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 968 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1475 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 968 = false ∨ valuation q 975 = true := counterClause1475 (baseVal q)

theorem counterClause1476 (q : Nat → Bool) : valuationOf q 961 = false ∨ valuationOf q 969 = false ∨ valuationOf q 976 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (961)) (literal (valuationOf q) (969)) (literal (valuationOf q) (976)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 3 3 (meaning961 q) (meaning969 q) (meaning976 q) hs
  change valuationOf q 961 = false ∨ valuationOf q 969 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1476 (q : Snake 81) (h : Conditions q) : valuation q 961 = false ∨ valuation q 969 = false ∨ valuation q 976 = true := counterClause1476 (baseVal q)

theorem counterClause1477 (q : Nat → Bool) : valuationOf q 962 = false ∨ valuationOf q 967 = false ∨ valuationOf q 975 = true := by
  have hs : count971 q = (countLit q [-50, -51, -54, -56]) + (countLit q [-59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-50, -51, -54, -56]) (l₂ := [-59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (962)) (literal (valuationOf q) (967)) (literal (valuationOf q) (975)) (countLit q [-50, -51, -54, -56]) (countLit q [-59, -60, -61, -64]) (count971 q) 4 1 (meaning962 q) (meaning967 q) (meaning975 q) hs
  change valuationOf q 962 = false ∨ valuationOf q 967 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1477 (q : Snake 81) (h : Conditions q) : valuation q 962 = false ∨ valuation q 967 = false ∨ valuation q 975 = true := counterClause1477 (baseVal q)

theorem counterClause1478 (q : Nat → Bool) : valuationOf q 974 = false ∨ valuationOf q 982 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_right (literal (valuationOf q) (974)) (literal (valuationOf q) (982)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 4 (meaning974 q) (meaning982 q) hs
  change valuationOf q 974 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1478 (q : Snake 81) (h : Conditions q) : valuation q 974 = false ∨ valuation q 982 = true := counterClause1478 (baseVal q)

theorem counterClause1479 (q : Nat → Bool) : valuationOf q 976 = false ∨ valuationOf q 984 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_right (literal (valuationOf q) (976)) (literal (valuationOf q) (984)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 6 (meaning976 q) (meaning984 q) hs
  change valuationOf q 976 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1479 (q : Snake 81) (h : Conditions q) : valuation q 976 = false ∨ valuation q 984 = true := counterClause1479 (baseVal q)

theorem counterClause1480 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 972 = false ∨ valuationOf q 981 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (972)) (literal (valuationOf q) (981)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 1 2 (meaning947 q) (meaning972 q) (meaning981 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 972 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1480 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 972 = false ∨ valuation q 981 = true := counterClause1480 (baseVal q)

theorem counterClause1481 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 973 = false ∨ valuationOf q 982 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (973)) (literal (valuationOf q) (982)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 1 3 (meaning947 q) (meaning973 q) (meaning982 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 973 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1481 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 973 = false ∨ valuation q 982 = true := counterClause1481 (baseVal q)

theorem counterClause1482 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 974 = false ∨ valuationOf q 983 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (974)) (literal (valuationOf q) (983)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 1 4 (meaning947 q) (meaning974 q) (meaning983 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 974 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1482 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 974 = false ∨ valuation q 983 = true := counterClause1482 (baseVal q)

theorem counterClause1483 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 975 = false ∨ valuationOf q 984 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (975)) (literal (valuationOf q) (984)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 1 5 (meaning947 q) (meaning975 q) (meaning984 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 975 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1483 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 975 = false ∨ valuation q 984 = true := counterClause1483 (baseVal q)

theorem counterClause1484 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 976 = false ∨ valuationOf q 985 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (976)) (literal (valuationOf q) (985)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 1 6 (meaning947 q) (meaning976 q) (meaning985 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 976 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1484 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 976 = false ∨ valuation q 985 = true := counterClause1484 (baseVal q)

theorem counterClause1485 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 972 = false ∨ valuationOf q 982 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (972)) (literal (valuationOf q) (982)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 2 2 (meaning948 q) (meaning972 q) (meaning982 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 972 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1485 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 972 = false ∨ valuation q 982 = true := counterClause1485 (baseVal q)

theorem counterClause1486 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 973 = false ∨ valuationOf q 983 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (973)) (literal (valuationOf q) (983)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 2 3 (meaning948 q) (meaning973 q) (meaning983 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 973 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1486 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 973 = false ∨ valuation q 983 = true := counterClause1486 (baseVal q)

theorem counterClause1487 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 974 = false ∨ valuationOf q 984 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (974)) (literal (valuationOf q) (984)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 2 4 (meaning948 q) (meaning974 q) (meaning984 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 974 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1487 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 974 = false ∨ valuation q 984 = true := counterClause1487 (baseVal q)

theorem counterClause1488 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 975 = false ∨ valuationOf q 985 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (975)) (literal (valuationOf q) (985)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 2 5 (meaning948 q) (meaning975 q) (meaning985 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 975 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1488 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 975 = false ∨ valuation q 985 = true := counterClause1488 (baseVal q)

theorem counterClause1489 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 976 = false ∨ valuationOf q 986 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (976)) (literal (valuationOf q) (986)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 2 6 (meaning948 q) (meaning976 q) (meaning986 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 976 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1489 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 976 = false ∨ valuation q 986 = true := counterClause1489 (baseVal q)

theorem counterClause1490 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 971 = false ∨ valuationOf q 982 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (971)) (literal (valuationOf q) (982)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 3 1 (meaning949 q) (meaning971 q) (meaning982 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 971 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1490 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 971 = false ∨ valuation q 982 = true := counterClause1490 (baseVal q)

theorem counterClause1491 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 972 = false ∨ valuationOf q 983 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (972)) (literal (valuationOf q) (983)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 3 2 (meaning949 q) (meaning972 q) (meaning983 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 972 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1491 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 972 = false ∨ valuation q 983 = true := counterClause1491 (baseVal q)

theorem counterClause1492 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 973 = false ∨ valuationOf q 984 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (973)) (literal (valuationOf q) (984)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 3 3 (meaning949 q) (meaning973 q) (meaning984 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 973 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1492 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 973 = false ∨ valuation q 984 = true := counterClause1492 (baseVal q)

theorem counterClause1493 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 974 = false ∨ valuationOf q 985 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (974)) (literal (valuationOf q) (985)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 3 4 (meaning949 q) (meaning974 q) (meaning985 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 974 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1493 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 974 = false ∨ valuation q 985 = true := counterClause1493 (baseVal q)

theorem counterClause1494 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 976 = false ∨ valuationOf q 987 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (976)) (literal (valuationOf q) (987)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 3 6 (meaning949 q) (meaning976 q) (meaning987 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 976 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1494 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 976 = false ∨ valuation q 987 = true := counterClause1494 (baseVal q)

theorem counterClause1495 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 971 = false ∨ valuationOf q 983 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (971)) (literal (valuationOf q) (983)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 4 1 (meaning950 q) (meaning971 q) (meaning983 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 971 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1495 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 971 = false ∨ valuation q 983 = true := counterClause1495 (baseVal q)

theorem counterClause1496 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 972 = false ∨ valuationOf q 984 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (972)) (literal (valuationOf q) (984)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 4 2 (meaning950 q) (meaning972 q) (meaning984 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 972 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1496 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 972 = false ∨ valuation q 984 = true := counterClause1496 (baseVal q)

theorem counterClause1497 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 973 = false ∨ valuationOf q 985 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (973)) (literal (valuationOf q) (985)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 4 3 (meaning950 q) (meaning973 q) (meaning985 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 973 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1497 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 973 = false ∨ valuation q 985 = true := counterClause1497 (baseVal q)

theorem counterClause1498 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 974 = false ∨ valuationOf q 986 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (974)) (literal (valuationOf q) (986)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 4 4 (meaning950 q) (meaning974 q) (meaning986 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 974 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1498 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 974 = false ∨ valuation q 986 = true := counterClause1498 (baseVal q)

theorem counterClause1499 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 975 = false ∨ valuationOf q 987 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (950)) (literal (valuationOf q) (975)) (literal (valuationOf q) (987)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 4 5 (meaning950 q) (meaning975 q) (meaning987 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 975 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1499 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 975 = false ∨ valuation q 987 = true := counterClause1499 (baseVal q)

theorem counterClause1500 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 971 = false ∨ valuationOf q 984 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (951)) (literal (valuationOf q) (971)) (literal (valuationOf q) (984)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 5 1 (meaning951 q) (meaning971 q) (meaning984 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 971 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1500 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 971 = false ∨ valuation q 984 = true := counterClause1500 (baseVal q)

theorem counterClause1501 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 972 = false ∨ valuationOf q 985 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (951)) (literal (valuationOf q) (972)) (literal (valuationOf q) (985)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 5 2 (meaning951 q) (meaning972 q) (meaning985 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 972 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1501 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 972 = false ∨ valuation q 985 = true := counterClause1501 (baseVal q)

theorem counterClause1502 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 973 = false ∨ valuationOf q 986 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (951)) (literal (valuationOf q) (973)) (literal (valuationOf q) (986)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 5 3 (meaning951 q) (meaning973 q) (meaning986 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 973 = false ∨ valuationOf q 986 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1502 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 973 = false ∨ valuation q 986 = true := counterClause1502 (baseVal q)

theorem counterClause1503 (q : Nat → Bool) : valuationOf q 951 = false ∨ valuationOf q 974 = false ∨ valuationOf q 987 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (951)) (literal (valuationOf q) (974)) (literal (valuationOf q) (987)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 5 4 (meaning951 q) (meaning974 q) (meaning987 q) hs
  change valuationOf q 951 = false ∨ valuationOf q 974 = false ∨ valuationOf q 987 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1503 (q : Snake 81) (h : Conditions q) : valuation q 951 = false ∨ valuation q 974 = false ∨ valuation q 987 = true := counterClause1503 (baseVal q)

theorem counterClause1504 (q : Nat → Bool) : valuationOf q 952 = false ∨ valuationOf q 971 = false ∨ valuationOf q 985 = true := by
  have hs : count979 q = (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) + (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42, -43, -46, -47, -48]) (l₂ := [-50, -51, -54, -56, -59, -60, -61, -64])
  have hm := merge_two (literal (valuationOf q) (952)) (literal (valuationOf q) (971)) (literal (valuationOf q) (985)) (countLit q [-35, -36, -39, -42, -43, -46, -47, -48]) (countLit q [-50, -51, -54, -56, -59, -60, -61, -64]) (count979 q) 6 1 (meaning952 q) (meaning971 q) (meaning985 q) hs
  change valuationOf q 952 = false ∨ valuationOf q 971 = false ∨ valuationOf q 985 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1504 (q : Snake 81) (h : Conditions q) : valuation q 952 = false ∨ valuation q 971 = false ∨ valuation q 985 = true := counterClause1504 (baseVal q)

theorem block46 (q : Snake 81) (h : Conditions q) : B112E057.Block46 (valuation q) :=
  ⟨clause1473 q h, clause1474 q h, clause1475 q h, clause1476 q h, clause1477 q h, clause1478 q h, clause1479 q h, clause1480 q h, clause1481 q h, clause1482 q h, clause1483 q h, clause1484 q h, clause1485 q h, clause1486 q h, clause1487 q h, clause1488 q h, clause1489 q h, clause1490 q h, clause1491 q h, clause1492 q h, clause1493 q h, clause1494 q h, clause1495 q h, clause1496 q h, clause1497 q h, clause1498 q h, clause1499 q h, clause1500 q h, clause1501 q h, clause1502 q h, clause1503 q h, clause1504 q h⟩

end
end Snake9.Regrowth.E112057
