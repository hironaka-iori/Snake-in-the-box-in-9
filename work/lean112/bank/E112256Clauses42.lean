import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 944 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (944)) (literal (valuationOf q) (955)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 3 1 (meaning923 q) (meaning944 q) (meaning955 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 944 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 944 = false ∨ valuation q 955 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 945 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (945)) (literal (valuationOf q) (956)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 3 2 (meaning923 q) (meaning945 q) (meaning956 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 945 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 945 = false ∨ valuation q 956 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 946 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (946)) (literal (valuationOf q) (957)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 3 3 (meaning923 q) (meaning946 q) (meaning957 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 946 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 946 = false ∨ valuation q 957 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 947 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (947)) (literal (valuationOf q) (958)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 3 4 (meaning923 q) (meaning947 q) (meaning958 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 947 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 947 = false ∨ valuation q 958 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 948 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (948)) (literal (valuationOf q) (959)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 3 5 (meaning923 q) (meaning948 q) (meaning959 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 948 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 948 = false ∨ valuation q 959 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 949 = false ∨ valuationOf q 960 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (949)) (literal (valuationOf q) (960)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 3 6 (meaning923 q) (meaning949 q) (meaning960 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 949 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 949 = false ∨ valuation q 960 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_left (literal (valuationOf q) (924)) (literal (valuationOf q) (955)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 4 (meaning924 q) (meaning955 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 955 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 944 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (944)) (literal (valuationOf q) (956)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 4 1 (meaning924 q) (meaning944 q) (meaning956 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 944 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 944 = false ∨ valuation q 956 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 945 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (945)) (literal (valuationOf q) (957)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 4 2 (meaning924 q) (meaning945 q) (meaning957 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 945 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 945 = false ∨ valuation q 957 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 946 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (946)) (literal (valuationOf q) (958)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 4 3 (meaning924 q) (meaning946 q) (meaning958 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 946 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 946 = false ∨ valuation q 958 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 947 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (947)) (literal (valuationOf q) (959)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 4 4 (meaning924 q) (meaning947 q) (meaning959 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 947 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 947 = false ∨ valuation q 959 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 948 = false ∨ valuationOf q 960 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (948)) (literal (valuationOf q) (960)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 4 5 (meaning924 q) (meaning948 q) (meaning960 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 948 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 948 = false ∨ valuation q 960 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 949 = false ∨ valuationOf q 961 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (949)) (literal (valuationOf q) (961)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 4 6 (meaning924 q) (meaning949 q) (meaning961 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 949 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 949 = false ∨ valuation q 961 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_left (literal (valuationOf q) (925)) (literal (valuationOf q) (956)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 5 (meaning925 q) (meaning956 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 956 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 944 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (944)) (literal (valuationOf q) (957)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 5 1 (meaning925 q) (meaning944 q) (meaning957 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 944 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 944 = false ∨ valuation q 957 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 945 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (945)) (literal (valuationOf q) (958)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 5 2 (meaning925 q) (meaning945 q) (meaning958 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 945 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 945 = false ∨ valuation q 958 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 946 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (946)) (literal (valuationOf q) (959)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 5 3 (meaning925 q) (meaning946 q) (meaning959 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 946 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 946 = false ∨ valuation q 959 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 947 = false ∨ valuationOf q 960 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (947)) (literal (valuationOf q) (960)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 5 4 (meaning925 q) (meaning947 q) (meaning960 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 947 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 947 = false ∨ valuation q 960 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 948 = false ∨ valuationOf q 961 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (948)) (literal (valuationOf q) (961)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 5 5 (meaning925 q) (meaning948 q) (meaning961 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 948 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 948 = false ∨ valuation q 961 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 949 = false ∨ valuationOf q 962 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (949)) (literal (valuationOf q) (962)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 5 6 (meaning925 q) (meaning949 q) (meaning962 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 949 = false ∨ valuationOf q 962 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 949 = false ∨ valuation q 962 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_left (literal (valuationOf q) (926)) (literal (valuationOf q) (957)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 6 (meaning926 q) (meaning957 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 957 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 944 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (944)) (literal (valuationOf q) (958)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 6 1 (meaning926 q) (meaning944 q) (meaning958 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 944 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 944 = false ∨ valuation q 958 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 945 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (945)) (literal (valuationOf q) (959)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 6 2 (meaning926 q) (meaning945 q) (meaning959 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 945 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 945 = false ∨ valuation q 959 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 946 = false ∨ valuationOf q 960 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (946)) (literal (valuationOf q) (960)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 6 3 (meaning926 q) (meaning946 q) (meaning960 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 946 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 946 = false ∨ valuation q 960 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 947 = false ∨ valuationOf q 961 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (926)) (literal (valuationOf q) (947)) (literal (valuationOf q) (961)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 6 4 (meaning926 q) (meaning947 q) (meaning961 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 947 = false ∨ valuationOf q 961 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 947 = false ∨ valuation q 961 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 927 = false ∨ valuationOf q 944 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-33, -34, -36, -41, -42, -43, -44]) + (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-33, -34, -36, -41, -42, -43, -44]) (l₂ := [-45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (927)) (literal (valuationOf q) (944)) (literal (valuationOf q) (959)) (countLit q [-33, -34, -36, -41, -42, -43, -44]) (countLit q [-45, -47, -49, -53, -57, -58, -60, -61]) (count952 q) 7 1 (meaning927 q) (meaning944 q) (meaning959 q) hs
  change valuationOf q 927 = false ∨ valuationOf q 944 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 927 = false ∨ valuation q 944 = false ∨ valuation q 959 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 893 = false ∨ valuationOf q 961 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (893)) (literal (valuationOf q) (961)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 1 10 (meaning893 q) (meaning961 q) (meaning977 q) hs
  change valuationOf q 893 = false ∨ valuationOf q 961 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 893 = false ∨ valuation q 961 = false ∨ valuation q 977 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 956 = false ∨ valuationOf q 973 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (956)) (literal (valuationOf q) (973)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 2 5 (meaning894 q) (meaning956 q) (meaning973 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 956 = false ∨ valuationOf q 973 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 956 = false ∨ valuation q 973 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 957 = false ∨ valuationOf q 974 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (957)) (literal (valuationOf q) (974)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 2 6 (meaning894 q) (meaning957 q) (meaning974 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 957 = false ∨ valuationOf q 974 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 957 = false ∨ valuation q 974 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 958 = false ∨ valuationOf q 975 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (958)) (literal (valuationOf q) (975)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 2 7 (meaning894 q) (meaning958 q) (meaning975 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 958 = false ∨ valuationOf q 975 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 958 = false ∨ valuation q 975 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 959 = false ∨ valuationOf q 976 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (959)) (literal (valuationOf q) (976)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 2 8 (meaning894 q) (meaning959 q) (meaning976 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 959 = false ∨ valuationOf q 976 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 959 = false ∨ valuation q 976 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 894 = false ∨ valuationOf q 960 = false ∨ valuationOf q 977 = true := by
  have hs : count967 q = (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) + (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) := List.countP_append (p := literal q) (l₁ := [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (l₂ := [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61])
  have hm := merge_two (literal (valuationOf q) (894)) (literal (valuationOf q) (960)) (literal (valuationOf q) (977)) (countLit q [-1, -2, -5, -7, -10, -11, -14, -15, -18, -19, -21, -23, -25, -28, -30]) (countLit q [-33, -34, -36, -41, -42, -43, -44, -45, -47, -49, -53, -57, -58, -60, -61]) (count967 q) 2 9 (meaning894 q) (meaning960 q) (meaning977 q) hs
  change valuationOf q 894 = false ∨ valuationOf q 960 = false ∨ valuationOf q 977 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 894 = false ∨ valuation q 960 = false ∨ valuation q 977 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E256.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112256
