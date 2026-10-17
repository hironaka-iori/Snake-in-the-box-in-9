import E112161Semantics
import B112E161Inputs
namespace Snake9.Regrowth.E112161
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1356 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1356)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 2 3 (meaning1342 q) (meaning1350 q) (meaning1356 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1350 = false ∨ valuation q 1356 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 1342 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1357 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1342)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1357)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 2 4 (meaning1342 q) (meaning1351 q) (meaning1357 q) hs
  change valuationOf q 1342 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 1342 = false ∨ valuation q 1351 = false ∨ valuation q 1357 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1354 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_left (literal (valuationOf q) (1343)) (literal (valuationOf q) (1354)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 3 (meaning1343 q) (meaning1354 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1354 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1355 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1348)) (literal (valuationOf q) (1355)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 3 1 (meaning1343 q) (meaning1348 q) (meaning1355 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1348 = false ∨ valuationOf q 1355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1348 = false ∨ valuation q 1355 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1356 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1349)) (literal (valuationOf q) (1356)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 3 2 (meaning1343 q) (meaning1349 q) (meaning1356 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1349 = false ∨ valuationOf q 1356 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1349 = false ∨ valuation q 1356 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1357 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1350)) (literal (valuationOf q) (1357)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 3 3 (meaning1343 q) (meaning1350 q) (meaning1357 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1350 = false ∨ valuationOf q 1357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1350 = false ∨ valuation q 1357 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 1343 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1358 = true := by
  have hs : count1352 q = (countLit q [-17, -19, -21]) + (countLit q [-22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -21]) (l₂ := [-22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1343)) (literal (valuationOf q) (1351)) (literal (valuationOf q) (1358)) (countLit q [-17, -19, -21]) (countLit q [-22, -24, -25, -29]) (count1352 q) 3 4 (meaning1343 q) (meaning1351 q) (meaning1358 q) hs
  change valuationOf q 1343 = false ∨ valuationOf q 1351 = false ∨ valuationOf q 1358 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 1343 = false ∨ valuation q 1351 = false ∨ valuation q 1358 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 1353 = false ∨ valuationOf q 1360 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_right (literal (valuationOf q) (1353)) (literal (valuationOf q) (1360)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 2 (meaning1353 q) (meaning1360 q) hs
  change valuationOf q 1353 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 1353 = false ∨ valuation q 1360 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 1354 = false ∨ valuationOf q 1361 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_right (literal (valuationOf q) (1354)) (literal (valuationOf q) (1361)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 3 (meaning1354 q) (meaning1361 q) hs
  change valuationOf q 1354 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 1354 = false ∨ valuation q 1361 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1356 = false ∨ valuationOf q 1363 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_right (literal (valuationOf q) (1356)) (literal (valuationOf q) (1363)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 5 (meaning1356 q) (meaning1363 q) hs
  change valuationOf q 1356 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1356 = false ∨ valuation q 1363 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1360 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1360)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 1 1 (meaning1332 q) (meaning1352 q) (meaning1360 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1360 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1352 = false ∨ valuation q 1360 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1361 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1361)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 1 2 (meaning1332 q) (meaning1353 q) (meaning1361 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1353 = false ∨ valuation q 1361 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1362 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1362)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 1 3 (meaning1332 q) (meaning1354 q) (meaning1362 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1354 = false ∨ valuation q 1362 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1363 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1363)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 1 4 (meaning1332 q) (meaning1355 q) (meaning1363 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1355 = false ∨ valuation q 1363 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1364 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1364)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 1 5 (meaning1332 q) (meaning1356 q) (meaning1364 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1356 = false ∨ valuation q 1364 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1365 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1365)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 1 6 (meaning1332 q) (meaning1357 q) (meaning1365 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1357 = false ∨ valuation q 1365 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 1332 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1366 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1332)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1366)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 1 7 (meaning1332 q) (meaning1358 q) (meaning1366 q) hs
  change valuationOf q 1332 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1332 = false ∨ valuation q 1358 = false ∨ valuation q 1366 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1361 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1361)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 2 1 (meaning1333 q) (meaning1352 q) (meaning1361 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1352 = false ∨ valuation q 1361 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1362 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1362)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 2 2 (meaning1333 q) (meaning1353 q) (meaning1362 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1362 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1353 = false ∨ valuation q 1362 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1363 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1363)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 2 3 (meaning1333 q) (meaning1354 q) (meaning1363 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1354 = false ∨ valuation q 1363 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1364 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1364)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 2 4 (meaning1333 q) (meaning1355 q) (meaning1364 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1355 = false ∨ valuation q 1364 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1365 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1365)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 2 5 (meaning1333 q) (meaning1356 q) (meaning1365 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1356 = false ∨ valuation q 1365 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1366 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1366)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 2 6 (meaning1333 q) (meaning1357 q) (meaning1366 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1357 = false ∨ valuation q 1366 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1333 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1367 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1333)) (literal (valuationOf q) (1358)) (literal (valuationOf q) (1367)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 2 7 (meaning1333 q) (meaning1358 q) (meaning1367 q) hs
  change valuationOf q 1333 = false ∨ valuationOf q 1358 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1333 = false ∨ valuation q 1358 = false ∨ valuation q 1367 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1363 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1363)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 3 2 (meaning1334 q) (meaning1353 q) (meaning1363 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1353 = false ∨ valuation q 1363 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1364 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1364)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 3 3 (meaning1334 q) (meaning1354 q) (meaning1364 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1354 = false ∨ valuation q 1364 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1365 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1355)) (literal (valuationOf q) (1365)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 3 4 (meaning1334 q) (meaning1355 q) (meaning1365 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1355 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1355 = false ∨ valuation q 1365 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1366 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1356)) (literal (valuationOf q) (1366)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 3 5 (meaning1334 q) (meaning1356 q) (meaning1366 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1356 = false ∨ valuationOf q 1366 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1356 = false ∨ valuation q 1366 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 1334 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1367 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1334)) (literal (valuationOf q) (1357)) (literal (valuationOf q) (1367)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 3 6 (meaning1334 q) (meaning1357 q) (meaning1367 q) hs
  change valuationOf q 1334 = false ∨ valuationOf q 1357 = false ∨ valuationOf q 1367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 1334 = false ∨ valuation q 1357 = false ∨ valuation q 1367 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1363 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1352)) (literal (valuationOf q) (1363)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 4 1 (meaning1335 q) (meaning1352 q) (meaning1363 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1352 = false ∨ valuationOf q 1363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1352 = false ∨ valuation q 1363 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1364 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1353)) (literal (valuationOf q) (1364)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 4 2 (meaning1335 q) (meaning1353 q) (meaning1364 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1353 = false ∨ valuationOf q 1364 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1353 = false ∨ valuation q 1364 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 1335 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1365 = true := by
  have hs : count1359 q = (countLit q [-2, -6, -8, -10, -12, -14, -16]) + (countLit q [-17, -19, -21, -22, -24, -25, -29]) := List.countP_append (p := literal q) (l₁ := [-2, -6, -8, -10, -12, -14, -16]) (l₂ := [-17, -19, -21, -22, -24, -25, -29])
  have hm := merge_two (literal (valuationOf q) (1335)) (literal (valuationOf q) (1354)) (literal (valuationOf q) (1365)) (countLit q [-2, -6, -8, -10, -12, -14, -16]) (countLit q [-17, -19, -21, -22, -24, -25, -29]) (count1359 q) 4 3 (meaning1335 q) (meaning1354 q) (meaning1365 q) hs
  change valuationOf q 1335 = false ∨ valuationOf q 1354 = false ∨ valuationOf q 1365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 1335 = false ∨ valuation q 1354 = false ∨ valuation q 1365 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E161.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112161
