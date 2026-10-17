import E112058Semantics
import B112E058Inputs
namespace Snake9.Regrowth.E112058
noncomputable section
local instance blockDec10 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause321 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1403 = true := by
  have hs : count1403 q = (countLit q [-2]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -6])
  have hm := merge_left (literal (valuationOf q) (-2)) (literal (valuationOf q) (1403)) (countLit q [-2]) (countLit q [-5, -6]) (count1403 q) 1 (meaningNeg2 q) (meaning1403 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause321 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1403 = true := counterClause321 (baseVal q)

theorem counterClause322 (q : Nat → Bool) : valuationOf q 2 = true ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true := by
  have hs : count1403 q = (countLit q [-2]) + (countLit q [-5, -6]) := List.countP_append (p := literal q) (l₁ := [-2]) (l₂ := [-5, -6])
  have hm := merge_two (literal (valuationOf q) (-2)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1404)) (countLit q [-2]) (countLit q [-5, -6]) (count1403 q) 1 1 (meaningNeg2 q) (meaning1401 q) (meaning1404 q) hs
  change (! (valuationOf q 2)) = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause322 (q : Snake 81) (h : Conditions q) : valuation q 2 = true ∨ valuation q 1401 = false ∨ valuation q 1404 = true := counterClause322 (baseVal q)

theorem counterClause323 (q : Nat → Bool) : valuationOf q 10 = true ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-10]) + (countLit q [-11]) := List.countP_append (p := literal q) (l₁ := [-10]) (l₂ := [-11])
  have hm := merge_left (literal (valuationOf q) (-10)) (literal (valuationOf q) (1406)) (countLit q [-10]) (countLit q [-11]) (count1406 q) 1 (meaningNeg10 q) (meaning1406 q) hs
  change (! (valuationOf q 10)) = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause323 (q : Snake 81) (h : Conditions q) : valuation q 10 = true ∨ valuation q 1406 = true := counterClause323 (baseVal q)

theorem counterClause324 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1408 = true := by
  have hs : count1408 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (1408)) (countLit q [-13]) (countLit q [-15]) (count1408 q) 1 (meaningNeg15 q) (meaning1408 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause324 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1408 = true := counterClause324 (baseVal q)

theorem counterClause325 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 1408 = true := by
  have hs : count1408 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-13)) (literal (valuationOf q) (1408)) (countLit q [-13]) (countLit q [-15]) (count1408 q) 1 (meaningNeg13 q) (meaning1408 q) hs
  change (! (valuationOf q 13)) = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause325 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 1408 = true := counterClause325 (baseVal q)

theorem counterClause326 (q : Nat → Bool) : valuationOf q 13 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1409 = true := by
  have hs : count1408 q = (countLit q [-13]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-13]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-13)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1409)) (countLit q [-13]) (countLit q [-15]) (count1408 q) 1 1 (meaningNeg13 q) (meaningNeg15 q) (meaning1409 q) hs
  change (! (valuationOf q 13)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause326 (q : Snake 81) (h : Conditions q) : valuation q 13 = true ∨ valuation q 15 = true ∨ valuation q 1409 = true := counterClause326 (baseVal q)

theorem counterClause327 (q : Nat → Bool) : valuationOf q 1408 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-10, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-10, -11]) (l₂ := [-13, -15])
  have hm := merge_right (literal (valuationOf q) (1408)) (literal (valuationOf q) (1410)) (countLit q [-10, -11]) (countLit q [-13, -15]) (count1410 q) 1 (meaning1408 q) (meaning1410 q) hs
  change valuationOf q 1408 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause327 (q : Snake 81) (h : Conditions q) : valuation q 1408 = false ∨ valuation q 1410 = true := counterClause327 (baseVal q)

theorem counterClause328 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-10, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-10, -11]) (l₂ := [-13, -15])
  have hm := merge_right (literal (valuationOf q) (1409)) (literal (valuationOf q) (1411)) (countLit q [-10, -11]) (countLit q [-13, -15]) (count1410 q) 2 (meaning1409 q) (meaning1411 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause328 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1411 = true := counterClause328 (baseVal q)

theorem counterClause329 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-10, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-10, -11]) (l₂ := [-13, -15])
  have hm := merge_left (literal (valuationOf q) (1406)) (literal (valuationOf q) (1410)) (countLit q [-10, -11]) (countLit q [-13, -15]) (count1410 q) 1 (meaning1406 q) (meaning1410 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause329 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1410 = true := counterClause329 (baseVal q)

theorem counterClause330 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-10, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-10, -11]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1411)) (countLit q [-10, -11]) (countLit q [-13, -15]) (count1410 q) 1 1 (meaning1406 q) (meaning1408 q) (meaning1411 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause330 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1408 = false ∨ valuation q 1411 = true := counterClause330 (baseVal q)

theorem counterClause331 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-10, -11]) + (countLit q [-13, -15]) := List.countP_append (p := literal q) (l₁ := [-10, -11]) (l₂ := [-13, -15])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1412)) (countLit q [-10, -11]) (countLit q [-13, -15]) (count1410 q) 1 2 (meaning1406 q) (meaning1409 q) (meaning1412 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause331 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1409 = false ∨ valuation q 1412 = true := counterClause331 (baseVal q)

theorem counterClause332 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-2, -5, -6]) + (countLit q [-10, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-10, -11, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1410)) (literal (valuationOf q) (1414)) (countLit q [-2, -5, -6]) (countLit q [-10, -11, -13, -15]) (count1414 q) 1 (meaning1410 q) (meaning1414 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause332 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1414 = true := counterClause332 (baseVal q)

theorem counterClause333 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-2, -5, -6]) + (countLit q [-10, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-10, -11, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1411)) (literal (valuationOf q) (1415)) (countLit q [-2, -5, -6]) (countLit q [-10, -11, -13, -15]) (count1414 q) 2 (meaning1411 q) (meaning1415 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause333 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1415 = true := counterClause333 (baseVal q)

theorem counterClause334 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-2, -5, -6]) + (countLit q [-10, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-10, -11, -13, -15])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1416)) (countLit q [-2, -5, -6]) (countLit q [-10, -11, -13, -15]) (count1414 q) 3 (meaning1412 q) (meaning1416 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause334 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1416 = true := counterClause334 (baseVal q)

theorem counterClause335 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-2, -5, -6]) + (countLit q [-10, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-10, -11, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1403)) (literal (valuationOf q) (1414)) (countLit q [-2, -5, -6]) (countLit q [-10, -11, -13, -15]) (count1414 q) 1 (meaning1403 q) (meaning1414 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause335 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1414 = true := counterClause335 (baseVal q)

theorem counterClause336 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-2, -5, -6]) + (countLit q [-10, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-10, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1415)) (countLit q [-2, -5, -6]) (countLit q [-10, -11, -13, -15]) (count1414 q) 1 1 (meaning1403 q) (meaning1410 q) (meaning1415 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause336 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1410 = false ∨ valuation q 1415 = true := counterClause336 (baseVal q)

theorem counterClause337 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-2, -5, -6]) + (countLit q [-10, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-10, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1416)) (countLit q [-2, -5, -6]) (countLit q [-10, -11, -13, -15]) (count1414 q) 1 2 (meaning1403 q) (meaning1411 q) (meaning1416 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause337 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1411 = false ∨ valuation q 1416 = true := counterClause337 (baseVal q)

theorem counterClause338 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-2, -5, -6]) + (countLit q [-10, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-10, -11, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1404)) (literal (valuationOf q) (1415)) (countLit q [-2, -5, -6]) (countLit q [-10, -11, -13, -15]) (count1414 q) 2 (meaning1404 q) (meaning1415 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause338 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1415 = true := counterClause338 (baseVal q)

theorem counterClause339 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-2, -5, -6]) + (countLit q [-10, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -5, -6]) (l₂ := [-10, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1416)) (countLit q [-2, -5, -6]) (countLit q [-10, -11, -13, -15]) (count1414 q) 2 1 (meaning1404 q) (meaning1410 q) (meaning1416 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause339 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1410 = false ∨ valuation q 1416 = true := counterClause339 (baseVal q)

theorem counterClause340 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1421)) (countLit q [-20]) (countLit q [-22]) (count1421 q) 1 (meaningNeg22 q) (meaning1421 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause340 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1421 = true := counterClause340 (baseVal q)

theorem counterClause341 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-20)) (literal (valuationOf q) (1421)) (countLit q [-20]) (countLit q [-22]) (count1421 q) 1 (meaningNeg20 q) (meaning1421 q) hs
  change (! (valuationOf q 20)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause341 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 1421 = true := counterClause341 (baseVal q)

theorem counterClause342 (q : Nat → Bool) : valuationOf q 20 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-20]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-20]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-20)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1422)) (countLit q [-20]) (countLit q [-22]) (count1421 q) 1 1 (meaningNeg20 q) (meaningNeg22 q) (meaning1422 q) hs
  change (! (valuationOf q 20)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause342 (q : Snake 81) (h : Conditions q) : valuation q 20 = true ∨ valuation q 22 = true ∨ valuation q 1422 = true := counterClause342 (baseVal q)

theorem counterClause343 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-18]) + (countLit q [-20, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20, -22])
  have hm := merge_right (literal (valuationOf q) (1421)) (literal (valuationOf q) (1423)) (countLit q [-18]) (countLit q [-20, -22]) (count1423 q) 1 (meaning1421 q) (meaning1423 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause343 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1423 = true := counterClause343 (baseVal q)

theorem counterClause344 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-18]) + (countLit q [-20, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20, -22])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1424)) (countLit q [-18]) (countLit q [-20, -22]) (count1423 q) 2 (meaning1422 q) (meaning1424 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause344 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1424 = true := counterClause344 (baseVal q)

theorem counterClause345 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-18]) + (countLit q [-20, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20, -22])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1423)) (countLit q [-18]) (countLit q [-20, -22]) (count1423 q) 1 (meaningNeg18 q) (meaning1423 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause345 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1423 = true := counterClause345 (baseVal q)

theorem counterClause346 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-18]) + (countLit q [-20, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20, -22])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1424)) (countLit q [-18]) (countLit q [-20, -22]) (count1423 q) 1 1 (meaningNeg18 q) (meaning1421 q) (meaning1424 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause346 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1421 = false ∨ valuation q 1424 = true := counterClause346 (baseVal q)

theorem counterClause347 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1422 = false ∨ valuationOf q 1425 = true := by
  have hs : count1423 q = (countLit q [-18]) + (countLit q [-20, -22]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-20, -22])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1425)) (countLit q [-18]) (countLit q [-20, -22]) (count1423 q) 1 2 (meaningNeg18 q) (meaning1422 q) (meaning1425 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause347 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1422 = false ∨ valuation q 1425 = true := counterClause347 (baseVal q)

theorem counterClause348 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1426)) (countLit q [-23]) (countLit q [-24]) (count1426 q) 1 (meaningNeg24 q) (meaning1426 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause348 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1426 = true := counterClause348 (baseVal q)

theorem counterClause349 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1426 = true := by
  have hs : count1426 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1426)) (countLit q [-23]) (countLit q [-24]) (count1426 q) 1 (meaningNeg23 q) (meaning1426 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause349 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1426 = true := counterClause349 (baseVal q)

theorem counterClause350 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1427 = true := by
  have hs : count1426 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1427)) (countLit q [-23]) (countLit q [-24]) (count1426 q) 1 1 (meaningNeg23 q) (meaningNeg24 q) (meaning1427 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause350 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 1427 = true := counterClause350 (baseVal q)

theorem counterClause351 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1428)) (countLit q [-27]) (countLit q [-30]) (count1428 q) 1 (meaningNeg30 q) (meaning1428 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause351 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1428 = true := counterClause351 (baseVal q)

theorem counterClause352 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1428 = true := by
  have hs : count1428 q = (countLit q [-27]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1428)) (countLit q [-27]) (countLit q [-30]) (count1428 q) 1 (meaningNeg27 q) (meaning1428 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause352 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1428 = true := counterClause352 (baseVal q)

theorem block10 (q : Snake 81) (h : Conditions q) : B112E058.Block10 (valuation q) :=
  ⟨clause321 q h, clause322 q h, clause323 q h, clause324 q h, clause325 q h, clause326 q h, clause327 q h, clause328 q h, clause329 q h, clause330 q h, clause331 q h, clause332 q h, clause333 q h, clause334 q h, clause335 q h, clause336 q h, clause337 q h, clause338 q h, clause339 q h, clause340 q h, clause341 q h, clause342 q h, clause343 q h, clause344 q h, clause345 q h, clause346 q h, clause347 q h, clause348 q h, clause349 q h, clause350 q h, clause351 q h, clause352 q h⟩

end
end Snake9.Regrowth.E112058
