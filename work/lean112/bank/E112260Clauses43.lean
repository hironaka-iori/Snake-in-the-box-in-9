import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec43 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1377 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 945 = false ∨ valuationOf q 954 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (945)) (literal (valuationOf q) (954)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 1 2 (meaning921 q) (meaning945 q) (meaning954 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 945 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1377 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 945 = false ∨ valuation q 954 = true := counterClause1377 (baseVal q)

theorem counterClause1378 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 946 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (946)) (literal (valuationOf q) (955)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 1 3 (meaning921 q) (meaning946 q) (meaning955 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 946 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1378 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 946 = false ∨ valuation q 955 = true := counterClause1378 (baseVal q)

theorem counterClause1379 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 947 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (947)) (literal (valuationOf q) (956)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 1 4 (meaning921 q) (meaning947 q) (meaning956 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 947 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1379 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 947 = false ∨ valuation q 956 = true := counterClause1379 (baseVal q)

theorem counterClause1380 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 948 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (948)) (literal (valuationOf q) (957)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 1 5 (meaning921 q) (meaning948 q) (meaning957 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 948 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1380 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 948 = false ∨ valuation q 957 = true := counterClause1380 (baseVal q)

theorem counterClause1381 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 949 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (949)) (literal (valuationOf q) (958)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 1 6 (meaning921 q) (meaning949 q) (meaning958 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 949 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1381 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 949 = false ∨ valuation q 958 = true := counterClause1381 (baseVal q)

theorem counterClause1382 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 950 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (950)) (literal (valuationOf q) (959)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 1 7 (meaning921 q) (meaning950 q) (meaning959 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 950 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1382 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 950 = false ∨ valuation q 959 = true := counterClause1382 (baseVal q)

theorem counterClause1383 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 953 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (922)) (literal (valuationOf q) (953)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 2 (meaning922 q) (meaning953 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1383 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 953 = true := counterClause1383 (baseVal q)

theorem counterClause1384 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 944 = false ∨ valuationOf q 954 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (944)) (literal (valuationOf q) (954)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 2 1 (meaning922 q) (meaning944 q) (meaning954 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 944 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1384 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 944 = false ∨ valuation q 954 = true := counterClause1384 (baseVal q)

theorem counterClause1385 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 945 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (945)) (literal (valuationOf q) (955)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 2 2 (meaning922 q) (meaning945 q) (meaning955 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 945 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1385 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 945 = false ∨ valuation q 955 = true := counterClause1385 (baseVal q)

theorem counterClause1386 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 946 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (946)) (literal (valuationOf q) (956)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 2 3 (meaning922 q) (meaning946 q) (meaning956 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 946 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1386 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 946 = false ∨ valuation q 956 = true := counterClause1386 (baseVal q)

theorem counterClause1387 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 947 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (947)) (literal (valuationOf q) (957)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 2 4 (meaning922 q) (meaning947 q) (meaning957 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 947 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1387 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 947 = false ∨ valuation q 957 = true := counterClause1387 (baseVal q)

theorem counterClause1388 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 948 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (948)) (literal (valuationOf q) (958)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 2 5 (meaning922 q) (meaning948 q) (meaning958 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 948 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1388 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 948 = false ∨ valuation q 958 = true := counterClause1388 (baseVal q)

theorem counterClause1389 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 949 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (949)) (literal (valuationOf q) (959)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 2 6 (meaning922 q) (meaning949 q) (meaning959 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 949 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1389 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 949 = false ∨ valuation q 959 = true := counterClause1389 (baseVal q)

theorem counterClause1390 (q : Nat → Bool) : valuationOf q 922 = false ∨ valuationOf q 950 = false ∨ valuationOf q 960 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (922)) (literal (valuationOf q) (950)) (literal (valuationOf q) (960)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 2 7 (meaning922 q) (meaning950 q) (meaning960 q) hs
  change valuationOf q 922 = false ∨ valuationOf q 950 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1390 (q : Snake 81) (h : Conditions q) : valuation q 922 = false ∨ valuation q 950 = false ∨ valuation q 960 = true := counterClause1390 (baseVal q)

theorem counterClause1391 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 954 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (923)) (literal (valuationOf q) (954)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 3 (meaning923 q) (meaning954 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1391 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 954 = true := counterClause1391 (baseVal q)

theorem counterClause1392 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 944 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (944)) (literal (valuationOf q) (955)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 3 1 (meaning923 q) (meaning944 q) (meaning955 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 944 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1392 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 944 = false ∨ valuation q 955 = true := counterClause1392 (baseVal q)

theorem counterClause1393 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 945 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (945)) (literal (valuationOf q) (956)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 3 2 (meaning923 q) (meaning945 q) (meaning956 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 945 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1393 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 945 = false ∨ valuation q 956 = true := counterClause1393 (baseVal q)

theorem counterClause1394 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 946 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (946)) (literal (valuationOf q) (957)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 3 3 (meaning923 q) (meaning946 q) (meaning957 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 946 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1394 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 946 = false ∨ valuation q 957 = true := counterClause1394 (baseVal q)

theorem counterClause1395 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 947 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (947)) (literal (valuationOf q) (958)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 3 4 (meaning923 q) (meaning947 q) (meaning958 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 947 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1395 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 947 = false ∨ valuation q 958 = true := counterClause1395 (baseVal q)

theorem counterClause1396 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 948 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (948)) (literal (valuationOf q) (959)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 3 5 (meaning923 q) (meaning948 q) (meaning959 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 948 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1396 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 948 = false ∨ valuation q 959 = true := counterClause1396 (baseVal q)

theorem counterClause1397 (q : Nat → Bool) : valuationOf q 923 = false ∨ valuationOf q 949 = false ∨ valuationOf q 960 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (923)) (literal (valuationOf q) (949)) (literal (valuationOf q) (960)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 3 6 (meaning923 q) (meaning949 q) (meaning960 q) hs
  change valuationOf q 923 = false ∨ valuationOf q 949 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1397 (q : Snake 81) (h : Conditions q) : valuation q 923 = false ∨ valuation q 949 = false ∨ valuation q 960 = true := counterClause1397 (baseVal q)

theorem counterClause1398 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (924)) (literal (valuationOf q) (955)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 4 (meaning924 q) (meaning955 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1398 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 955 = true := counterClause1398 (baseVal q)

theorem counterClause1399 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 944 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (944)) (literal (valuationOf q) (956)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 4 1 (meaning924 q) (meaning944 q) (meaning956 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 944 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1399 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 944 = false ∨ valuation q 956 = true := counterClause1399 (baseVal q)

theorem counterClause1400 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 945 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (945)) (literal (valuationOf q) (957)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 4 2 (meaning924 q) (meaning945 q) (meaning957 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 945 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1400 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 945 = false ∨ valuation q 957 = true := counterClause1400 (baseVal q)

theorem counterClause1401 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 946 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (946)) (literal (valuationOf q) (958)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 4 3 (meaning924 q) (meaning946 q) (meaning958 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 946 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1401 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 946 = false ∨ valuation q 958 = true := counterClause1401 (baseVal q)

theorem counterClause1402 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 947 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (947)) (literal (valuationOf q) (959)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 4 4 (meaning924 q) (meaning947 q) (meaning959 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 947 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1402 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 947 = false ∨ valuation q 959 = true := counterClause1402 (baseVal q)

theorem counterClause1403 (q : Nat → Bool) : valuationOf q 924 = false ∨ valuationOf q 948 = false ∨ valuationOf q 960 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (924)) (literal (valuationOf q) (948)) (literal (valuationOf q) (960)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 4 5 (meaning924 q) (meaning948 q) (meaning960 q) hs
  change valuationOf q 924 = false ∨ valuationOf q 948 = false ∨ valuationOf q 960 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1403 (q : Snake 81) (h : Conditions q) : valuation q 924 = false ∨ valuation q 948 = false ∨ valuation q 960 = true := counterClause1403 (baseVal q)

theorem counterClause1404 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (925)) (literal (valuationOf q) (956)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 5 (meaning925 q) (meaning956 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1404 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 956 = true := counterClause1404 (baseVal q)

theorem counterClause1405 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 944 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (944)) (literal (valuationOf q) (957)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 5 1 (meaning925 q) (meaning944 q) (meaning957 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 944 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1405 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 944 = false ∨ valuation q 957 = true := counterClause1405 (baseVal q)

theorem counterClause1406 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 945 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (945)) (literal (valuationOf q) (958)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 5 2 (meaning925 q) (meaning945 q) (meaning958 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 945 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1406 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 945 = false ∨ valuation q 958 = true := counterClause1406 (baseVal q)

theorem counterClause1407 (q : Nat → Bool) : valuationOf q 925 = false ∨ valuationOf q 946 = false ∨ valuationOf q 959 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (925)) (literal (valuationOf q) (946)) (literal (valuationOf q) (959)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 5 3 (meaning925 q) (meaning946 q) (meaning959 q) hs
  change valuationOf q 925 = false ∨ valuationOf q 946 = false ∨ valuationOf q 959 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1407 (q : Snake 81) (h : Conditions q) : valuation q 925 = false ∨ valuation q 946 = false ∨ valuation q 959 = true := counterClause1407 (baseVal q)

theorem counterClause1408 (q : Nat → Bool) : valuationOf q 926 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (926)) (literal (valuationOf q) (957)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 6 (meaning926 q) (meaning957 q) hs
  change valuationOf q 926 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1408 (q : Snake 81) (h : Conditions q) : valuation q 926 = false ∨ valuation q 957 = true := counterClause1408 (baseVal q)

theorem block43 (q : Snake 81) (h : Conditions q) : B112E260.Block43 (valuation q) :=
  ⟨clause1377 q h, clause1378 q h, clause1379 q h, clause1380 q h, clause1381 q h, clause1382 q h, clause1383 q h, clause1384 q h, clause1385 q h, clause1386 q h, clause1387 q h, clause1388 q h, clause1389 q h, clause1390 q h, clause1391 q h, clause1392 q h, clause1393 q h, clause1394 q h, clause1395 q h, clause1396 q h, clause1397 q h, clause1398 q h, clause1399 q h, clause1400 q h, clause1401 q h, clause1402 q h, clause1403 q h, clause1404 q h, clause1405 q h, clause1406 q h, clause1407 q h, clause1408 q h⟩

end
end Snake9.Regrowth.E112260
