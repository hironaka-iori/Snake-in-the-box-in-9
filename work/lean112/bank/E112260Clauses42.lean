import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec42 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1345 (q : Nat → Bool) : valuationOf q 940 = false ∨ valuationOf q 944 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (940)) (literal (valuationOf q) (944)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 1 (meaning940 q) (meaning944 q) hs
  change valuationOf q 940 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1345 (q : Snake 81) (h : Conditions q) : valuation q 940 = false ∨ valuation q 944 = true := counterClause1345 (baseVal q)

theorem counterClause1346 (q : Nat → Bool) : valuationOf q 941 = false ∨ valuationOf q 945 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (941)) (literal (valuationOf q) (945)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 2 (meaning941 q) (meaning945 q) hs
  change valuationOf q 941 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1346 (q : Snake 81) (h : Conditions q) : valuation q 941 = false ∨ valuation q 945 = true := counterClause1346 (baseVal q)

theorem counterClause1347 (q : Nat → Bool) : valuationOf q 942 = false ∨ valuationOf q 946 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (942)) (literal (valuationOf q) (946)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 3 (meaning942 q) (meaning946 q) hs
  change valuationOf q 942 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1347 (q : Snake 81) (h : Conditions q) : valuation q 942 = false ∨ valuation q 946 = true := counterClause1347 (baseVal q)

theorem counterClause1348 (q : Nat → Bool) : valuationOf q 943 = false ∨ valuationOf q 947 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (943)) (literal (valuationOf q) (947)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 4 (meaning943 q) (meaning947 q) hs
  change valuationOf q 943 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1348 (q : Snake 81) (h : Conditions q) : valuation q 943 = false ∨ valuation q 947 = true := counterClause1348 (baseVal q)

theorem counterClause1349 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 944 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (932)) (literal (valuationOf q) (944)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 1 (meaning932 q) (meaning944 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 944 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1349 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 944 = true := counterClause1349 (baseVal q)

theorem counterClause1350 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (940)) (literal (valuationOf q) (945)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 1 1 (meaning932 q) (meaning940 q) (meaning945 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 940 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1350 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 940 = false ∨ valuation q 945 = true := counterClause1350 (baseVal q)

theorem counterClause1351 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 941 = false ∨ valuationOf q 946 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (941)) (literal (valuationOf q) (946)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 1 2 (meaning932 q) (meaning941 q) (meaning946 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 941 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1351 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 941 = false ∨ valuation q 946 = true := counterClause1351 (baseVal q)

theorem counterClause1352 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 942 = false ∨ valuationOf q 947 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (942)) (literal (valuationOf q) (947)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 1 3 (meaning932 q) (meaning942 q) (meaning947 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 942 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1352 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 942 = false ∨ valuation q 947 = true := counterClause1352 (baseVal q)

theorem counterClause1353 (q : Nat → Bool) : valuationOf q 932 = false ∨ valuationOf q 943 = false ∨ valuationOf q 948 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (932)) (literal (valuationOf q) (943)) (literal (valuationOf q) (948)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 1 4 (meaning932 q) (meaning943 q) (meaning948 q) hs
  change valuationOf q 932 = false ∨ valuationOf q 943 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1353 (q : Snake 81) (h : Conditions q) : valuation q 932 = false ∨ valuation q 943 = false ∨ valuation q 948 = true := counterClause1353 (baseVal q)

theorem counterClause1354 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 945 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (933)) (literal (valuationOf q) (945)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 2 (meaning933 q) (meaning945 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 945 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1354 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 945 = true := counterClause1354 (baseVal q)

theorem counterClause1355 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (940)) (literal (valuationOf q) (946)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 2 1 (meaning933 q) (meaning940 q) (meaning946 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 940 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1355 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 940 = false ∨ valuation q 946 = true := counterClause1355 (baseVal q)

theorem counterClause1356 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 941 = false ∨ valuationOf q 947 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (941)) (literal (valuationOf q) (947)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 2 2 (meaning933 q) (meaning941 q) (meaning947 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 941 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1356 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 941 = false ∨ valuation q 947 = true := counterClause1356 (baseVal q)

theorem counterClause1357 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 942 = false ∨ valuationOf q 948 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (942)) (literal (valuationOf q) (948)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 2 3 (meaning933 q) (meaning942 q) (meaning948 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 942 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1357 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 942 = false ∨ valuation q 948 = true := counterClause1357 (baseVal q)

theorem counterClause1358 (q : Nat → Bool) : valuationOf q 933 = false ∨ valuationOf q 943 = false ∨ valuationOf q 949 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (933)) (literal (valuationOf q) (943)) (literal (valuationOf q) (949)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 2 4 (meaning933 q) (meaning943 q) (meaning949 q) hs
  change valuationOf q 933 = false ∨ valuationOf q 943 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1358 (q : Snake 81) (h : Conditions q) : valuation q 933 = false ∨ valuation q 943 = false ∨ valuation q 949 = true := counterClause1358 (baseVal q)

theorem counterClause1359 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 946 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (934)) (literal (valuationOf q) (946)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 3 (meaning934 q) (meaning946 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 946 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1359 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 946 = true := counterClause1359 (baseVal q)

theorem counterClause1360 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (940)) (literal (valuationOf q) (947)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 3 1 (meaning934 q) (meaning940 q) (meaning947 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 940 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1360 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 940 = false ∨ valuation q 947 = true := counterClause1360 (baseVal q)

theorem counterClause1361 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 941 = false ∨ valuationOf q 948 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (941)) (literal (valuationOf q) (948)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 3 2 (meaning934 q) (meaning941 q) (meaning948 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 941 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1361 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 941 = false ∨ valuation q 948 = true := counterClause1361 (baseVal q)

theorem counterClause1362 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 942 = false ∨ valuationOf q 949 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (942)) (literal (valuationOf q) (949)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 3 3 (meaning934 q) (meaning942 q) (meaning949 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 942 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1362 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 942 = false ∨ valuation q 949 = true := counterClause1362 (baseVal q)

theorem counterClause1363 (q : Nat → Bool) : valuationOf q 934 = false ∨ valuationOf q 943 = false ∨ valuationOf q 950 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (934)) (literal (valuationOf q) (943)) (literal (valuationOf q) (950)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 3 4 (meaning934 q) (meaning943 q) (meaning950 q) hs
  change valuationOf q 934 = false ∨ valuationOf q 943 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1363 (q : Snake 81) (h : Conditions q) : valuation q 934 = false ∨ valuation q 943 = false ∨ valuation q 950 = true := counterClause1363 (baseVal q)

theorem counterClause1364 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 947 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (935)) (literal (valuationOf q) (947)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 4 (meaning935 q) (meaning947 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 947 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1364 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 947 = true := counterClause1364 (baseVal q)

theorem counterClause1365 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 940 = false ∨ valuationOf q 948 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (940)) (literal (valuationOf q) (948)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 4 1 (meaning935 q) (meaning940 q) (meaning948 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 940 = false ∨ valuationOf q 948 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1365 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 940 = false ∨ valuation q 948 = true := counterClause1365 (baseVal q)

theorem counterClause1366 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 941 = false ∨ valuationOf q 949 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (941)) (literal (valuationOf q) (949)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 4 2 (meaning935 q) (meaning941 q) (meaning949 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 941 = false ∨ valuationOf q 949 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1366 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 941 = false ∨ valuation q 949 = true := counterClause1366 (baseVal q)

theorem counterClause1367 (q : Nat → Bool) : valuationOf q 935 = false ∨ valuationOf q 942 = false ∨ valuationOf q 950 = true := by
  have hs : count944 q = (countLit q [-48, -49, -50, -51]) + (countLit q [-56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-48, -49, -50, -51]) (l₂ := [-56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (935)) (literal (valuationOf q) (942)) (literal (valuationOf q) (950)) (countLit q [-48, -49, -50, -51]) (countLit q [-56, -60, -62, -64]) (count944 q) 4 3 (meaning935 q) (meaning942 q) (meaning950 q) hs
  change valuationOf q 935 = false ∨ valuationOf q 942 = false ∨ valuationOf q 950 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1367 (q : Snake 81) (h : Conditions q) : valuation q 935 = false ∨ valuation q 942 = false ∨ valuation q 950 = true := counterClause1367 (baseVal q)

theorem counterClause1368 (q : Nat → Bool) : valuationOf q 944 = false ∨ valuationOf q 952 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (944)) (literal (valuationOf q) (952)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 1 (meaning944 q) (meaning952 q) hs
  change valuationOf q 944 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1368 (q : Snake 81) (h : Conditions q) : valuation q 944 = false ∨ valuation q 952 = true := counterClause1368 (baseVal q)

theorem counterClause1369 (q : Nat → Bool) : valuationOf q 945 = false ∨ valuationOf q 953 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (945)) (literal (valuationOf q) (953)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 2 (meaning945 q) (meaning953 q) hs
  change valuationOf q 945 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1369 (q : Snake 81) (h : Conditions q) : valuation q 945 = false ∨ valuation q 953 = true := counterClause1369 (baseVal q)

theorem counterClause1370 (q : Nat → Bool) : valuationOf q 946 = false ∨ valuationOf q 954 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (946)) (literal (valuationOf q) (954)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 3 (meaning946 q) (meaning954 q) hs
  change valuationOf q 946 = false ∨ valuationOf q 954 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1370 (q : Snake 81) (h : Conditions q) : valuation q 946 = false ∨ valuation q 954 = true := counterClause1370 (baseVal q)

theorem counterClause1371 (q : Nat → Bool) : valuationOf q 947 = false ∨ valuationOf q 955 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (947)) (literal (valuationOf q) (955)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 4 (meaning947 q) (meaning955 q) hs
  change valuationOf q 947 = false ∨ valuationOf q 955 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1371 (q : Snake 81) (h : Conditions q) : valuation q 947 = false ∨ valuation q 955 = true := counterClause1371 (baseVal q)

theorem counterClause1372 (q : Nat → Bool) : valuationOf q 948 = false ∨ valuationOf q 956 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (948)) (literal (valuationOf q) (956)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 5 (meaning948 q) (meaning956 q) hs
  change valuationOf q 948 = false ∨ valuationOf q 956 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1372 (q : Snake 81) (h : Conditions q) : valuation q 948 = false ∨ valuation q 956 = true := counterClause1372 (baseVal q)

theorem counterClause1373 (q : Nat → Bool) : valuationOf q 949 = false ∨ valuationOf q 957 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (949)) (literal (valuationOf q) (957)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 6 (meaning949 q) (meaning957 q) hs
  change valuationOf q 949 = false ∨ valuationOf q 957 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1373 (q : Snake 81) (h : Conditions q) : valuation q 949 = false ∨ valuation q 957 = true := counterClause1373 (baseVal q)

theorem counterClause1374 (q : Nat → Bool) : valuationOf q 950 = false ∨ valuationOf q 958 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_right (literal (valuationOf q) (950)) (literal (valuationOf q) (958)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 7 (meaning950 q) (meaning958 q) hs
  change valuationOf q 950 = false ∨ valuationOf q 958 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1374 (q : Snake 81) (h : Conditions q) : valuation q 950 = false ∨ valuation q 958 = true := counterClause1374 (baseVal q)

theorem counterClause1375 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 952 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_left (literal (valuationOf q) (921)) (literal (valuationOf q) (952)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 1 (meaning921 q) (meaning952 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 952 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1375 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 952 = true := counterClause1375 (baseVal q)

theorem counterClause1376 (q : Nat → Bool) : valuationOf q 921 = false ∨ valuationOf q 944 = false ∨ valuationOf q 953 = true := by
  have hs : count952 q = (countLit q [-32, -34, -36, -40, -42, -44, -46]) + (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) := List.countP_append (p := literal q) (l₁ := [-32, -34, -36, -40, -42, -44, -46]) (l₂ := [-48, -49, -50, -51, -56, -60, -62, -64])
  have hm := merge_two (literal (valuationOf q) (921)) (literal (valuationOf q) (944)) (literal (valuationOf q) (953)) (countLit q [-32, -34, -36, -40, -42, -44, -46]) (countLit q [-48, -49, -50, -51, -56, -60, -62, -64]) (count952 q) 1 1 (meaning921 q) (meaning944 q) (meaning953 q) hs
  change valuationOf q 921 = false ∨ valuationOf q 944 = false ∨ valuationOf q 953 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1376 (q : Snake 81) (h : Conditions q) : valuation q 921 = false ∨ valuation q 944 = false ∨ valuation q 953 = true := counterClause1376 (baseVal q)

theorem block42 (q : Snake 81) (h : Conditions q) : B112E260.Block42 (valuation q) :=
  ⟨clause1345 q h, clause1346 q h, clause1347 q h, clause1348 q h, clause1349 q h, clause1350 q h, clause1351 q h, clause1352 q h, clause1353 q h, clause1354 q h, clause1355 q h, clause1356 q h, clause1357 q h, clause1358 q h, clause1359 q h, clause1360 q h, clause1361 q h, clause1362 q h, clause1363 q h, clause1364 q h, clause1365 q h, clause1366 q h, clause1367 q h, clause1368 q h, clause1369 q h, clause1370 q h, clause1371 q h, clause1372 q h, clause1373 q h, clause1374 q h, clause1375 q h, clause1376 q h⟩

end
end Snake9.Regrowth.E112260
