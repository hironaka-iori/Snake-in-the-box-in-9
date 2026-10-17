import E112121Semantics
import B112E121Inputs
namespace Snake9.Regrowth.E112121
noncomputable section
local instance blockDec41 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1313 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 970 = false ∨ valuationOf q 980 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (944)) (literal (valuationOf q) (970)) (literal (valuationOf q) (980)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 2 4 (meaning944 q) (meaning970 q) (meaning980 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 970 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1313 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 970 = false ∨ valuation q 980 = true := counterClause1313 (baseVal q)

theorem counterClause1314 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 977 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_left (literal (valuationOf q) (945)) (literal (valuationOf q) (977)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 3 (meaning945 q) (meaning977 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1314 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 977 = true := counterClause1314 (baseVal q)

theorem counterClause1315 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 967 = false ∨ valuationOf q 978 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (967)) (literal (valuationOf q) (978)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 3 1 (meaning945 q) (meaning967 q) (meaning978 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 967 = false ∨ valuationOf q 978 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1315 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 967 = false ∨ valuation q 978 = true := counterClause1315 (baseVal q)

theorem counterClause1316 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 968 = false ∨ valuationOf q 979 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (968)) (literal (valuationOf q) (979)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 3 2 (meaning945 q) (meaning968 q) (meaning979 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 968 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1316 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 968 = false ∨ valuation q 979 = true := counterClause1316 (baseVal q)

theorem counterClause1317 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (969)) (literal (valuationOf q) (980)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 3 3 (meaning945 q) (meaning969 q) (meaning980 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 969 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1317 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 969 = false ∨ valuation q 980 = true := counterClause1317 (baseVal q)

theorem counterClause1318 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 970 = false ∨ valuationOf q 981 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (970)) (literal (valuationOf q) (981)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 3 4 (meaning945 q) (meaning970 q) (meaning981 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 970 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1318 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 970 = false ∨ valuation q 981 = true := counterClause1318 (baseVal q)

theorem counterClause1319 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 971 = false ∨ valuationOf q 982 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (971)) (literal (valuationOf q) (982)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 3 5 (meaning945 q) (meaning971 q) (meaning982 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 971 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1319 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 971 = false ∨ valuation q 982 = true := counterClause1319 (baseVal q)

theorem counterClause1320 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 972 = false ∨ valuationOf q 983 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (945)) (literal (valuationOf q) (972)) (literal (valuationOf q) (983)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 3 6 (meaning945 q) (meaning972 q) (meaning983 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 972 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1320 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 972 = false ∨ valuation q 983 = true := counterClause1320 (baseVal q)

theorem counterClause1321 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 967 = false ∨ valuationOf q 979 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (967)) (literal (valuationOf q) (979)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 4 1 (meaning946 q) (meaning967 q) (meaning979 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 967 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1321 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 967 = false ∨ valuation q 979 = true := counterClause1321 (baseVal q)

theorem counterClause1322 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 968 = false ∨ valuationOf q 980 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (968)) (literal (valuationOf q) (980)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 4 2 (meaning946 q) (meaning968 q) (meaning980 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 968 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1322 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 968 = false ∨ valuation q 980 = true := counterClause1322 (baseVal q)

theorem counterClause1323 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 969 = false ∨ valuationOf q 981 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (969)) (literal (valuationOf q) (981)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 4 3 (meaning946 q) (meaning969 q) (meaning981 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 969 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1323 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 969 = false ∨ valuation q 981 = true := counterClause1323 (baseVal q)

theorem counterClause1324 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 970 = false ∨ valuationOf q 982 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (970)) (literal (valuationOf q) (982)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 4 4 (meaning946 q) (meaning970 q) (meaning982 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 970 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1324 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 970 = false ∨ valuation q 982 = true := counterClause1324 (baseVal q)

theorem counterClause1325 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 971 = false ∨ valuationOf q 983 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (971)) (literal (valuationOf q) (983)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 4 5 (meaning946 q) (meaning971 q) (meaning983 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 971 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1325 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 971 = false ∨ valuation q 983 = true := counterClause1325 (baseVal q)

theorem counterClause1326 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 972 = false ∨ valuationOf q 984 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (946)) (literal (valuationOf q) (972)) (literal (valuationOf q) (984)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 4 6 (meaning946 q) (meaning972 q) (meaning984 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 972 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1326 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 972 = false ∨ valuation q 984 = true := counterClause1326 (baseVal q)

theorem counterClause1327 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 979 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_left (literal (valuationOf q) (947)) (literal (valuationOf q) (979)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 5 (meaning947 q) (meaning979 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 979 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1327 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 979 = true := counterClause1327 (baseVal q)

theorem counterClause1328 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 967 = false ∨ valuationOf q 980 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (967)) (literal (valuationOf q) (980)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 5 1 (meaning947 q) (meaning967 q) (meaning980 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 967 = false ∨ valuationOf q 980 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1328 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 967 = false ∨ valuation q 980 = true := counterClause1328 (baseVal q)

theorem counterClause1329 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 968 = false ∨ valuationOf q 981 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (968)) (literal (valuationOf q) (981)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 5 2 (meaning947 q) (meaning968 q) (meaning981 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 968 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1329 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 968 = false ∨ valuation q 981 = true := counterClause1329 (baseVal q)

theorem counterClause1330 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 969 = false ∨ valuationOf q 982 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (969)) (literal (valuationOf q) (982)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 5 3 (meaning947 q) (meaning969 q) (meaning982 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 969 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1330 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 969 = false ∨ valuation q 982 = true := counterClause1330 (baseVal q)

theorem counterClause1331 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 970 = false ∨ valuationOf q 983 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (947)) (literal (valuationOf q) (970)) (literal (valuationOf q) (983)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 5 4 (meaning947 q) (meaning970 q) (meaning983 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 970 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1331 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 970 = false ∨ valuation q 983 = true := counterClause1331 (baseVal q)

theorem counterClause1332 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 967 = false ∨ valuationOf q 981 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (967)) (literal (valuationOf q) (981)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 6 1 (meaning948 q) (meaning967 q) (meaning981 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 967 = false ∨ valuationOf q 981 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1332 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 967 = false ∨ valuation q 981 = true := counterClause1332 (baseVal q)

theorem counterClause1333 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 968 = false ∨ valuationOf q 982 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (968)) (literal (valuationOf q) (982)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 6 2 (meaning948 q) (meaning968 q) (meaning982 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 968 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1333 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 968 = false ∨ valuation q 982 = true := counterClause1333 (baseVal q)

theorem counterClause1334 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 969 = false ∨ valuationOf q 983 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (948)) (literal (valuationOf q) (969)) (literal (valuationOf q) (983)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 6 3 (meaning948 q) (meaning969 q) (meaning983 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 969 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1334 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 969 = false ∨ valuation q 983 = true := counterClause1334 (baseVal q)

theorem counterClause1335 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 967 = false ∨ valuationOf q 982 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (967)) (literal (valuationOf q) (982)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 7 1 (meaning949 q) (meaning967 q) (meaning982 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 967 = false ∨ valuationOf q 982 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1335 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 967 = false ∨ valuation q 982 = true := counterClause1335 (baseVal q)

theorem counterClause1336 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 968 = false ∨ valuationOf q 983 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (968)) (literal (valuationOf q) (983)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 7 2 (meaning949 q) (meaning968 q) (meaning983 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 968 = false ∨ valuationOf q 983 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1336 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 968 = false ∨ valuation q 983 = true := counterClause1336 (baseVal q)

theorem counterClause1337 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 969 = false ∨ valuationOf q 984 = true := by
  have hs : count975 q = (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) + (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -35, -36, -38, -42, -43, -44]) (l₂ := [-46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (949)) (literal (valuationOf q) (969)) (literal (valuationOf q) (984)) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44]) (countLit q [-46, -47, -51, -53, -54, -57, -59, -60]) (count975 q) 7 3 (meaning949 q) (meaning969 q) (meaning984 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 969 = false ∨ valuationOf q 984 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1337 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 969 = false ∨ valuation q 984 = true := counterClause1337 (baseVal q)

theorem counterClause1338 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 979 = false ∨ valuationOf q 999 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (979)) (literal (valuationOf q) (999)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 4 5 (meaning914 q) (meaning979 q) (meaning999 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 979 = false ∨ valuationOf q 999 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1338 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 979 = false ∨ valuation q 999 = true := counterClause1338 (baseVal q)

theorem counterClause1339 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1000 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (980)) (literal (valuationOf q) (1000)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 4 6 (meaning914 q) (meaning980 q) (meaning1000 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 980 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1339 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 980 = false ∨ valuation q 1000 = true := counterClause1339 (baseVal q)

theorem counterClause1340 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1001 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (981)) (literal (valuationOf q) (1001)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 4 7 (meaning914 q) (meaning981 q) (meaning1001 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 981 = false ∨ valuationOf q 1001 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1340 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 981 = false ∨ valuation q 1001 = true := counterClause1340 (baseVal q)

theorem counterClause1341 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1002 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (982)) (literal (valuationOf q) (1002)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 4 8 (meaning914 q) (meaning982 q) (meaning1002 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 982 = false ∨ valuationOf q 1002 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1341 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 982 = false ∨ valuation q 1002 = true := counterClause1341 (baseVal q)

theorem counterClause1342 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1003 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (983)) (literal (valuationOf q) (1003)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 4 9 (meaning914 q) (meaning983 q) (meaning1003 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 983 = false ∨ valuationOf q 1003 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1342 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 983 = false ∨ valuation q 1003 = true := counterClause1342 (baseVal q)

theorem counterClause1343 (q : Nat → Bool) : valuationOf q 914 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1004 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (914)) (literal (valuationOf q) (984)) (literal (valuationOf q) (1004)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 4 10 (meaning914 q) (meaning984 q) (meaning1004 q) hs
  change valuationOf q 914 = false ∨ valuationOf q 984 = false ∨ valuationOf q 1004 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1343 (q : Snake 81) (h : Conditions q) : valuation q 914 = false ∨ valuation q 984 = false ∨ valuation q 1004 = true := counterClause1343 (baseVal q)

theorem counterClause1344 (q : Nat → Bool) : valuationOf q 915 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1000 = true := by
  have hs : count991 q = (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) + (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) := List.countP_append (p := literal q) (l₁ := [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (l₂ := [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60])
  have hm := merge_two (literal (valuationOf q) (915)) (literal (valuationOf q) (979)) (literal (valuationOf q) (1000)) (countLit q [-1, -3, -4, -5, -9, -10, -11, -14, -15, -19, -22, -24, -25, -27, -28, -31]) (countLit q [-32, -34, -35, -36, -38, -42, -43, -44, -46, -47, -51, -53, -54, -57, -59, -60]) (count991 q) 5 5 (meaning915 q) (meaning979 q) (meaning1000 q) hs
  change valuationOf q 915 = false ∨ valuationOf q 979 = false ∨ valuationOf q 1000 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1344 (q : Snake 81) (h : Conditions q) : valuation q 915 = false ∨ valuation q 979 = false ∨ valuation q 1000 = true := counterClause1344 (baseVal q)

theorem block41 (q : Snake 81) (h : Conditions q) : B112E121.Block41 (valuation q) :=
  ⟨clause1313 q h, clause1314 q h, clause1315 q h, clause1316 q h, clause1317 q h, clause1318 q h, clause1319 q h, clause1320 q h, clause1321 q h, clause1322 q h, clause1323 q h, clause1324 q h, clause1325 q h, clause1326 q h, clause1327 q h, clause1328 q h, clause1329 q h, clause1330 q h, clause1331 q h, clause1332 q h, clause1333 q h, clause1334 q h, clause1335 q h, clause1336 q h, clause1337 q h, clause1338 q h, clause1339 q h, clause1340 q h, clause1341 q h, clause1342 q h, clause1343 q h, clause1344 q h⟩

end
end Snake9.Regrowth.E112121
