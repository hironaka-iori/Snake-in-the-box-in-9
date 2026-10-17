import E112057Semantics
import B112E057Inputs
namespace Snake9.Regrowth.E112057
noncomputable section
local instance blockDec44 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1409 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 944 = true := by
  have hs : count943 q = (countLit q [-43, -46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-47, -48])
  have hm := merge_right (literal (valuationOf q) (942)) (literal (valuationOf q) (944)) (countLit q [-43, -46]) (countLit q [-47, -48]) (count943 q) 2 (meaning942 q) (meaning944 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1409 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 944 = true := counterClause1409 (baseVal q)

theorem counterClause1410 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 943 = true := by
  have hs : count943 q = (countLit q [-43, -46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-47, -48])
  have hm := merge_left (literal (valuationOf q) (939)) (literal (valuationOf q) (943)) (countLit q [-43, -46]) (countLit q [-47, -48]) (count943 q) 1 (meaning939 q) (meaning943 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 943 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1410 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 943 = true := counterClause1410 (baseVal q)

theorem counterClause1411 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 941 = false ∨ valuationOf q 944 = true := by
  have hs : count943 q = (countLit q [-43, -46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (939)) (literal (valuationOf q) (941)) (literal (valuationOf q) (944)) (countLit q [-43, -46]) (countLit q [-47, -48]) (count943 q) 1 1 (meaning939 q) (meaning941 q) (meaning944 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 941 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1411 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 941 = false ∨ valuation q 944 = true := counterClause1411 (baseVal q)

theorem counterClause1412 (q : Nat → Bool) : valuationOf q 939 = false ∨ valuationOf q 942 = false ∨ valuationOf q 945 = true := by
  have hs : count943 q = (countLit q [-43, -46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (939)) (literal (valuationOf q) (942)) (literal (valuationOf q) (945)) (countLit q [-43, -46]) (countLit q [-47, -48]) (count943 q) 1 2 (meaning939 q) (meaning942 q) (meaning945 q) hs
  change valuationOf q 939 = false ∨ valuationOf q 942 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1412 (q : Snake 81) (h : Conditions q) : valuation q 939 = false ∨ valuation q 942 = false ∨ valuation q 945 = true := counterClause1412 (baseVal q)

theorem counterClause1413 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 944 = true := by
  have hs : count943 q = (countLit q [-43, -46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-47, -48])
  have hm := merge_left (literal (valuationOf q) (940)) (literal (valuationOf q) (944)) (countLit q [-43, -46]) (countLit q [-47, -48]) (count943 q) 2 (meaning940 q) (meaning944 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1413 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 944 = true := counterClause1413 (baseVal q)

theorem counterClause1414 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 941 = false ∨ valuationOf q 945 = true := by
  have hs : count943 q = (countLit q [-43, -46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (940)) (literal (valuationOf q) (941)) (literal (valuationOf q) (945)) (countLit q [-43, -46]) (countLit q [-47, -48]) (count943 q) 2 1 (meaning940 q) (meaning941 q) (meaning945 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 941 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1414 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 941 = false ∨ valuation q 945 = true := counterClause1414 (baseVal q)

theorem counterClause1415 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 942 = false ∨ valuationOf q 946 = true := by
  have hs : count943 q = (countLit q [-43, -46]) + (countLit q [-47, -48]) := List.countP_append (p := literal q) (l₁ := [-43, -46]) (l₂ := [-47, -48])
  have hm := merge_two (literal (valuationOf q) (940)) (literal (valuationOf q) (942)) (literal (valuationOf q) (946)) (countLit q [-43, -46]) (countLit q [-47, -48]) (count943 q) 2 2 (meaning940 q) (meaning942 q) (meaning946 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 942 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1415 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 942 = false ∨ valuation q 946 = true := counterClause1415 (baseVal q)

theorem counterClause1416 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 947 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_right (literal (valuationOf q) (943)) (literal (valuationOf q) (947)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 1 (meaning943 q) (meaning947 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1416 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 947 = true := counterClause1416 (baseVal q)

theorem counterClause1417 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 948 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_right (literal (valuationOf q) (944)) (literal (valuationOf q) (948)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 2 (meaning944 q) (meaning948 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1417 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 948 = true := counterClause1417 (baseVal q)

theorem counterClause1418 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 949 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_right (literal (valuationOf q) (945)) (literal (valuationOf q) (949)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 3 (meaning945 q) (meaning949 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1418 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 949 = true := counterClause1418 (baseVal q)

theorem counterClause1419 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 950 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_right (literal (valuationOf q) (946)) (literal (valuationOf q) (950)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 4 (meaning946 q) (meaning950 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1419 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 950 = true := counterClause1419 (baseVal q)

theorem counterClause1420 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 947 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_left (literal (valuationOf q) (935)) (literal (valuationOf q) (947)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 1 (meaning935 q) (meaning947 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1420 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 947 = true := counterClause1420 (baseVal q)

theorem counterClause1421 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 943 = false ∨ valuationOf q 948 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (943)) (literal (valuationOf q) (948)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 1 1 (meaning935 q) (meaning943 q) (meaning948 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 943 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1421 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 943 = false ∨ valuation q 948 = true := counterClause1421 (baseVal q)

theorem counterClause1422 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 944 = false ∨ valuationOf q 949 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (944)) (literal (valuationOf q) (949)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 1 2 (meaning935 q) (meaning944 q) (meaning949 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 944 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1422 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 944 = false ∨ valuation q 949 = true := counterClause1422 (baseVal q)

theorem counterClause1423 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 945 = false ∨ valuationOf q 950 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (945)) (literal (valuationOf q) (950)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 1 3 (meaning935 q) (meaning945 q) (meaning950 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 945 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1423 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 945 = false ∨ valuation q 950 = true := counterClause1423 (baseVal q)

theorem counterClause1424 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 948 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_left (literal (valuationOf q) (936)) (literal (valuationOf q) (948)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 2 (meaning936 q) (meaning948 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1424 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 948 = true := counterClause1424 (baseVal q)

theorem counterClause1425 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 943 = false ∨ valuationOf q 949 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (943)) (literal (valuationOf q) (949)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 2 1 (meaning936 q) (meaning943 q) (meaning949 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 943 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1425 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 943 = false ∨ valuation q 949 = true := counterClause1425 (baseVal q)

theorem counterClause1426 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 944 = false ∨ valuationOf q 950 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (944)) (literal (valuationOf q) (950)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 2 2 (meaning936 q) (meaning944 q) (meaning950 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 944 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1426 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 944 = false ∨ valuation q 950 = true := counterClause1426 (baseVal q)

theorem counterClause1427 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 945 = false ∨ valuationOf q 951 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (945)) (literal (valuationOf q) (951)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 2 3 (meaning936 q) (meaning945 q) (meaning951 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 945 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1427 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 945 = false ∨ valuation q 951 = true := counterClause1427 (baseVal q)

theorem counterClause1428 (q : Nat → Bool) : valuationOf q 936 = false ∨ valuationOf q 946 = false ∨ valuationOf q 952 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (936)) (literal (valuationOf q) (946)) (literal (valuationOf q) (952)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 2 4 (meaning936 q) (meaning946 q) (meaning952 q) hs
  change valuationOf q 936 = false ∨ valuationOf q 946 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1428 (q : Snake 81) (h : Conditions q) : valuation q 936 = false ∨ valuation q 946 = false ∨ valuation q 952 = true := counterClause1428 (baseVal q)

theorem counterClause1429 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 949 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_left (literal (valuationOf q) (937)) (literal (valuationOf q) (949)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 3 (meaning937 q) (meaning949 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1429 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 949 = true := counterClause1429 (baseVal q)

theorem counterClause1430 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 943 = false ∨ valuationOf q 950 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (937)) (literal (valuationOf q) (943)) (literal (valuationOf q) (950)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 3 1 (meaning937 q) (meaning943 q) (meaning950 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 943 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1430 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 943 = false ∨ valuation q 950 = true := counterClause1430 (baseVal q)

theorem counterClause1431 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 944 = false ∨ valuationOf q 951 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (937)) (literal (valuationOf q) (944)) (literal (valuationOf q) (951)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 3 2 (meaning937 q) (meaning944 q) (meaning951 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 944 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1431 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 944 = false ∨ valuation q 951 = true := counterClause1431 (baseVal q)

theorem counterClause1432 (q : Nat → Bool) : valuationOf q 937 = false ∨ valuationOf q 945 = false ∨ valuationOf q 952 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (937)) (literal (valuationOf q) (945)) (literal (valuationOf q) (952)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 3 3 (meaning937 q) (meaning945 q) (meaning952 q) hs
  change valuationOf q 937 = false ∨ valuationOf q 945 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1432 (q : Snake 81) (h : Conditions q) : valuation q 937 = false ∨ valuation q 945 = false ∨ valuation q 952 = true := counterClause1432 (baseVal q)

theorem counterClause1433 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 950 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_left (literal (valuationOf q) (938)) (literal (valuationOf q) (950)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 4 (meaning938 q) (meaning950 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1433 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 950 = true := counterClause1433 (baseVal q)

theorem counterClause1434 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 943 = false ∨ valuationOf q 951 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (938)) (literal (valuationOf q) (943)) (literal (valuationOf q) (951)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 4 1 (meaning938 q) (meaning943 q) (meaning951 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 943 = false ∨ valuationOf q 951 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1434 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 943 = false ∨ valuation q 951 = true := counterClause1434 (baseVal q)

theorem counterClause1435 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 944 = false ∨ valuationOf q 952 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (938)) (literal (valuationOf q) (944)) (literal (valuationOf q) (952)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 4 2 (meaning938 q) (meaning944 q) (meaning952 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 944 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1435 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 944 = false ∨ valuation q 952 = true := counterClause1435 (baseVal q)

theorem counterClause1436 (q : Nat → Bool) : valuationOf q 938 = false ∨ valuationOf q 946 = false ∨ valuationOf q 954 = true := by
  have hs : count947 q = (countLit q [-35, -36, -39, -42]) + (countLit q [-43, -46, -47, -48]) := List.countP_append (p := literal q) (l₁ := [-35, -36, -39, -42]) (l₂ := [-43, -46, -47, -48])
  have hm := merge_two (literal (valuationOf q) (938)) (literal (valuationOf q) (946)) (literal (valuationOf q) (954)) (countLit q [-35, -36, -39, -42]) (countLit q [-43, -46, -47, -48]) (count947 q) 4 4 (meaning938 q) (meaning946 q) (meaning954 q) hs
  change valuationOf q 938 = false ∨ valuationOf q 946 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1436 (q : Snake 81) (h : Conditions q) : valuation q 938 = false ∨ valuation q 946 = false ∨ valuation q 954 = true := counterClause1436 (baseVal q)

theorem counterClause1437 (q : Nat → Bool) : valuationOf q 51 = true ∨ valuationOf q 955 = true := by
  have hs : count955 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_right (literal (valuationOf q) (-51)) (literal (valuationOf q) (955)) (countLit q [-50]) (countLit q [-51]) (count955 q) 1 (meaningNeg51 q) (meaning955 q) hs
  change (! (valuationOf q 51)) = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1437 (q : Snake 81) (h : Conditions q) : valuation q 51 = true ∨ valuation q 955 = true := counterClause1437 (baseVal q)

theorem counterClause1438 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 955 = true := by
  have hs : count955 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_left (literal (valuationOf q) (-50)) (literal (valuationOf q) (955)) (countLit q [-50]) (countLit q [-51]) (count955 q) 1 (meaningNeg50 q) (meaning955 q) hs
  change (! (valuationOf q 50)) = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1438 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 955 = true := counterClause1438 (baseVal q)

theorem counterClause1439 (q : Nat → Bool) : valuationOf q 50 = true ∨ valuationOf q 51 = true ∨ valuationOf q 956 = true := by
  have hs : count955 q = (countLit q [-50]) + (countLit q [-51]) := List.countP_append (p := literal q) (l₁ := [-50]) (l₂ := [-51])
  have hm := merge_two (literal (valuationOf q) (-50)) (literal (valuationOf q) (-51)) (literal (valuationOf q) (956)) (countLit q [-50]) (countLit q [-51]) (count955 q) 1 1 (meaningNeg50 q) (meaningNeg51 q) (meaning956 q) hs
  change (! (valuationOf q 50)) = false ∨ (! (valuationOf q 51)) = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1439 (q : Snake 81) (h : Conditions q) : valuation q 50 = true ∨ valuation q 51 = true ∨ valuation q 956 = true := counterClause1439 (baseVal q)

theorem counterClause1440 (q : Nat → Bool) : valuationOf q 56 = true ∨ valuationOf q 957 = true := by
  have hs : count957 q = (countLit q [-54]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-56])
  have hm := merge_right (literal (valuationOf q) (-56)) (literal (valuationOf q) (957)) (countLit q [-54]) (countLit q [-56]) (count957 q) 1 (meaningNeg56 q) (meaning957 q) hs
  change (! (valuationOf q 56)) = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1440 (q : Snake 81) (h : Conditions q) : valuation q 56 = true ∨ valuation q 957 = true := counterClause1440 (baseVal q)

theorem block44 (q : Snake 81) (h : Conditions q) : B112E057.Block44 (valuation q) :=
  ⟨clause1409 q h, clause1410 q h, clause1411 q h, clause1412 q h, clause1413 q h, clause1414 q h, clause1415 q h, clause1416 q h, clause1417 q h, clause1418 q h, clause1419 q h, clause1420 q h, clause1421 q h, clause1422 q h, clause1423 q h, clause1424 q h, clause1425 q h, clause1426 q h, clause1427 q h, clause1428 q h, clause1429 q h, clause1430 q h, clause1431 q h, clause1432 q h, clause1433 q h, clause1434 q h, clause1435 q h, clause1436 q h, clause1437 q h, clause1438 q h, clause1439 q h, clause1440 q h⟩

end
end Snake9.Regrowth.E112057
