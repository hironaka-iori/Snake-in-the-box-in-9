import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec28 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause897 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1395)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1409)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 1 3 (meaning1395 q) (meaning1404 q) (meaning1409 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause897 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1404 = false ∨ valuation q 1409 = true := counterClause897 (baseVal q)

theorem counterClause898 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_left (literal (valuationOf q) (1396)) (literal (valuationOf q) (1407)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 2 (meaning1396 q) (meaning1407 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause898 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1407 = true := counterClause898 (baseVal q)

theorem counterClause899 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1408)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 2 1 (meaning1396 q) (meaning1402 q) (meaning1408 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause899 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1402 = false ∨ valuation q 1408 = true := counterClause899 (baseVal q)

theorem counterClause900 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1409)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 2 2 (meaning1396 q) (meaning1403 q) (meaning1409 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause900 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1403 = false ∨ valuation q 1409 = true := counterClause900 (baseVal q)

theorem counterClause901 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1410 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1410)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 2 3 (meaning1396 q) (meaning1404 q) (meaning1410 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause901 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1404 = false ∨ valuation q 1410 = true := counterClause901 (baseVal q)

theorem counterClause902 (q : Nat → Bool) : valuationOf q 1396 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1411 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1396)) (literal (valuationOf q) (1405)) (literal (valuationOf q) (1411)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 2 4 (meaning1396 q) (meaning1405 q) (meaning1411 q) hs
  change valuationOf q 1396 = false ∨ valuationOf q 1405 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause902 (q : Snake 81) (h : Conditions q) : valuation q 1396 = false ∨ valuation q 1405 = false ∨ valuation q 1411 = true := counterClause902 (baseVal q)

theorem counterClause903 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1408 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_left (literal (valuationOf q) (1397)) (literal (valuationOf q) (1408)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 3 (meaning1397 q) (meaning1408 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause903 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1408 = true := counterClause903 (baseVal q)

theorem counterClause904 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1409 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1397)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1409)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 3 1 (meaning1397 q) (meaning1402 q) (meaning1409 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause904 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1402 = false ∨ valuation q 1409 = true := counterClause904 (baseVal q)

theorem counterClause905 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1411 = true := by
  have hs : count1406 q = (countLit q [-45, -46, -47]) + (countLit q [-50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-45, -46, -47]) (l₂ := [-50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1397)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1411)) (countLit q [-45, -46, -47]) (countLit q [-50, -51, -53, -54]) (count1406 q) 3 3 (meaning1397 q) (meaning1404 q) (meaning1411 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause905 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1404 = false ∨ valuation q 1411 = true := counterClause905 (baseVal q)

theorem counterClause906 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1416 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_right (literal (valuationOf q) (1409)) (literal (valuationOf q) (1416)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 4 (meaning1409 q) (meaning1416 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause906 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1416 = true := counterClause906 (baseVal q)

theorem counterClause907 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1414 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1414)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 1 1 (meaning1386 q) (meaning1406 q) (meaning1414 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause907 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1406 = false ∨ valuation q 1414 = true := counterClause907 (baseVal q)

theorem counterClause908 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1415 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1415)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 1 2 (meaning1386 q) (meaning1407 q) (meaning1415 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause908 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1407 = false ∨ valuation q 1415 = true := counterClause908 (baseVal q)

theorem counterClause909 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1416 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1416)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 1 3 (meaning1386 q) (meaning1408 q) (meaning1416 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause909 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1408 = false ∨ valuation q 1416 = true := counterClause909 (baseVal q)

theorem counterClause910 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1417 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1417)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 1 4 (meaning1386 q) (meaning1409 q) (meaning1417 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause910 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1409 = false ∨ valuation q 1417 = true := counterClause910 (baseVal q)

theorem counterClause911 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1418)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 1 5 (meaning1386 q) (meaning1410 q) (meaning1418 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause911 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1410 = false ∨ valuation q 1418 = true := counterClause911 (baseVal q)

theorem counterClause912 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1419)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 1 6 (meaning1386 q) (meaning1411 q) (meaning1419 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause912 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1411 = false ∨ valuation q 1419 = true := counterClause912 (baseVal q)

theorem counterClause913 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1415 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1415)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 2 1 (meaning1387 q) (meaning1406 q) (meaning1415 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause913 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1406 = false ∨ valuation q 1415 = true := counterClause913 (baseVal q)

theorem counterClause914 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1416 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1416)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 2 2 (meaning1387 q) (meaning1407 q) (meaning1416 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause914 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1407 = false ∨ valuation q 1416 = true := counterClause914 (baseVal q)

theorem counterClause915 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1417 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1417)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 2 3 (meaning1387 q) (meaning1408 q) (meaning1417 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause915 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1408 = false ∨ valuation q 1417 = true := counterClause915 (baseVal q)

theorem counterClause916 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1418 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1418)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 2 4 (meaning1387 q) (meaning1409 q) (meaning1418 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause916 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1409 = false ∨ valuation q 1418 = true := counterClause916 (baseVal q)

theorem counterClause917 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1419)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 2 5 (meaning1387 q) (meaning1410 q) (meaning1419 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause917 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1410 = false ∨ valuation q 1419 = true := counterClause917 (baseVal q)

theorem counterClause918 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1416 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1416)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 3 1 (meaning1388 q) (meaning1406 q) (meaning1416 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause918 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1406 = false ∨ valuation q 1416 = true := counterClause918 (baseVal q)

theorem counterClause919 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1417 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1417)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 3 2 (meaning1388 q) (meaning1407 q) (meaning1417 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause919 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1407 = false ∨ valuation q 1417 = true := counterClause919 (baseVal q)

theorem counterClause920 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1418 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1418)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 3 3 (meaning1388 q) (meaning1408 q) (meaning1418 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause920 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1408 = false ∨ valuation q 1418 = true := counterClause920 (baseVal q)

theorem counterClause921 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1419)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 3 4 (meaning1388 q) (meaning1409 q) (meaning1419 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause921 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1409 = false ∨ valuation q 1419 = true := counterClause921 (baseVal q)

theorem counterClause922 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1417 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1417)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 4 1 (meaning1389 q) (meaning1406 q) (meaning1417 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause922 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1406 = false ∨ valuation q 1417 = true := counterClause922 (baseVal q)

theorem counterClause923 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1418 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1418)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 4 2 (meaning1389 q) (meaning1407 q) (meaning1418 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause923 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1407 = false ∨ valuation q 1418 = true := counterClause923 (baseVal q)

theorem counterClause924 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1389)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1419)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 4 3 (meaning1389 q) (meaning1408 q) (meaning1419 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause924 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1408 = false ∨ valuation q 1419 = true := counterClause924 (baseVal q)

theorem counterClause925 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1419 = true := by
  have hs : count1413 q = (countLit q [-30, -32, -33, -35, -39, -40, -42]) + (countLit q [-45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-30, -32, -33, -35, -39, -40, -42]) (l₂ := [-45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1419)) (countLit q [-30, -32, -33, -35, -39, -40, -42]) (countLit q [-45, -46, -47, -50, -51, -53, -54]) (count1413 q) 5 2 (meaning1390 q) (meaning1407 q) (meaning1419 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause925 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1407 = false ∨ valuation q 1419 = true := counterClause925 (baseVal q)

theorem counterClause926 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1415)) (literal (valuationOf q) (1431)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 2 3 (meaning1360 q) (meaning1415 q) (meaning1431 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1415 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause926 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1415 = false ∨ valuation q 1431 = true := counterClause926 (baseVal q)

theorem counterClause927 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1416)) (literal (valuationOf q) (1432)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 2 4 (meaning1360 q) (meaning1416 q) (meaning1432 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1416 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause927 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1416 = false ∨ valuation q 1432 = true := counterClause927 (baseVal q)

theorem counterClause928 (q : Nat → Bool) : valuationOf q 1360 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1434 = true := by
  have hs : count1427 q = (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) + (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (l₂ := [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54])
  have hm := merge_two (literal (valuationOf q) (1360)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1434)) (countLit q [-2, -6, -8, -10, -12, -14, -16, -17, -19, -21, -22, -24, -25, -29]) (countLit q [-30, -32, -33, -35, -39, -40, -42, -45, -46, -47, -50, -51, -53, -54]) (count1427 q) 2 6 (meaning1360 q) (meaning1418 q) (meaning1434 q) hs
  change valuationOf q 1360 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause928 (q : Snake 81) (h : Conditions q) : valuation q 1360 = false ∨ valuation q 1418 = false ∨ valuation q 1434 = true := counterClause928 (baseVal q)

theorem block28 (q : Snake 81) (h : Conditions q) : B112E161.Block28 (valuation q) :=
  ⟨clause897 q h, clause898 q h, clause899 q h, clause900 q h, clause901 q h, clause902 q h, clause903 q h, clause904 q h, clause905 q h, clause906 q h, clause907 q h, clause908 q h, clause909 q h, clause910 q h, clause911 q h, clause912 q h, clause913 q h, clause914 q h, clause915 q h, clause916 q h, clause917 q h, clause918 q h, clause919 q h, clause920 q h, clause921 q h, clause922 q h, clause923 q h, clause924 q h, clause925 q h, clause926 q h, clause927 q h, clause928 q h⟩

end
end Snake9.Regrowth.E112161
