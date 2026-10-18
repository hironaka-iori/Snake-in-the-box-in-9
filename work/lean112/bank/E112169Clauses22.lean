import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_right (literal (valuationOf q) (1409)) (literal (valuationOf q) (1411)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1410 q) 2 (meaning1409 q) (meaning1411 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1411 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (1406)) (literal (valuationOf q) (1410)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1410 q) 1 (meaning1406 q) (meaning1410 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1410 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1411)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1410 q) 1 1 (meaning1406 q) (meaning1408 q) (meaning1411 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1408 = false ∨ valuation q 1411 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1406)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1412)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1410 q) 1 2 (meaning1406 q) (meaning1409 q) (meaning1412 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1409 = false ∨ valuation q 1412 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_left (literal (valuationOf q) (1407)) (literal (valuationOf q) (1411)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1410 q) 2 (meaning1407 q) (meaning1411 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1411 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1408)) (literal (valuationOf q) (1412)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1410 q) 2 1 (meaning1407 q) (meaning1408 q) (meaning1412 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1408 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1408 = false ∨ valuation q 1412 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1413 = true := by
  have hs : count1410 q = (countLit q [-8, -9]) + (countLit q [-12, -13]) := List.countP_append (p := literal q) (l₁ := [-8, -9]) (l₂ := [-12, -13])
  have hm := merge_two (literal (valuationOf q) (1407)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1413)) (countLit q [-8, -9]) (countLit q [-12, -13]) (count1410 q) 2 2 (meaning1407 q) (meaning1409 q) (meaning1413 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1409 = false ∨ valuation q 1413 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1410)) (literal (valuationOf q) (1414)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 1 (meaning1410 q) (meaning1414 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1414 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1411 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1411)) (literal (valuationOf q) (1415)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 2 (meaning1411 q) (meaning1415 q) hs
  change valuationOf q 1411 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1411 = false ∨ valuation q 1415 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1416)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 3 (meaning1412 q) (meaning1416 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1416 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1413 = false ∨ valuationOf q 1417 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_right (literal (valuationOf q) (1413)) (literal (valuationOf q) (1417)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 4 (meaning1413 q) (meaning1417 q) hs
  change valuationOf q 1413 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1413 = false ∨ valuation q 1417 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1403)) (literal (valuationOf q) (1414)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 1 (meaning1403 q) (meaning1414 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1414 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1415)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 1 1 (meaning1403 q) (meaning1410 q) (meaning1415 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1410 = false ∨ valuation q 1415 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1416)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 1 2 (meaning1403 q) (meaning1411 q) (meaning1416 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1411 = false ∨ valuation q 1416 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1417 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1417)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 1 3 (meaning1403 q) (meaning1412 q) (meaning1417 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1412 = false ∨ valuation q 1417 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1418 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1418)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 1 4 (meaning1403 q) (meaning1413 q) (meaning1418 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1413 = false ∨ valuation q 1418 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1404)) (literal (valuationOf q) (1415)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 2 (meaning1404 q) (meaning1415 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1415 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1416)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 2 1 (meaning1404 q) (meaning1410 q) (meaning1416 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1410 = false ∨ valuation q 1416 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1417 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1417)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 2 2 (meaning1404 q) (meaning1411 q) (meaning1417 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1411 = false ∨ valuation q 1417 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1418 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1418)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 2 3 (meaning1404 q) (meaning1412 q) (meaning1418 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1412 = false ∨ valuation q 1418 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1419 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1419)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 2 4 (meaning1404 q) (meaning1413 q) (meaning1419 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1413 = false ∨ valuation q 1419 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1416 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_left (literal (valuationOf q) (1405)) (literal (valuationOf q) (1416)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 3 (meaning1405 q) (meaning1416 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1416 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1417 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1417)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 3 1 (meaning1405 q) (meaning1410 q) (meaning1417 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1410 = false ∨ valuation q 1417 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1418 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1418)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 3 2 (meaning1405 q) (meaning1411 q) (meaning1418 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1411 = false ∨ valuation q 1418 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1419 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1419)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 3 3 (meaning1405 q) (meaning1412 q) (meaning1419 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1412 = false ∨ valuation q 1419 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1420 = true := by
  have hs : count1414 q = (countLit q [-2, -4, -5]) + (countLit q [-8, -9, -12, -13]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5]) (l₂ := [-8, -9, -12, -13])
  have hm := merge_two (literal (valuationOf q) (1405)) (literal (valuationOf q) (1413)) (literal (valuationOf q) (1420)) (countLit q [-2, -4, -5]) (countLit q [-8, -9, -12, -13]) (count1414 q) 3 4 (meaning1405 q) (meaning1413 q) (meaning1420 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1413 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1413 = false ∨ valuation q 1420 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_right (literal (valuationOf q) (-19)) (literal (valuationOf q) (1421)) (countLit q [-18]) (countLit q [-19]) (count1421 q) 1 (meaningNeg19 q) (meaning1421 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1421 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_left (literal (valuationOf q) (-18)) (literal (valuationOf q) (1421)) (countLit q [-18]) (countLit q [-19]) (count1421 q) 1 (meaningNeg18 q) (meaning1421 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1421 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 19 = true ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-18]) + (countLit q [-19]) := List.countP_append (p := literal q) (l₁ := [-18]) (l₂ := [-19])
  have hm := merge_two (literal (valuationOf q) (-18)) (literal (valuationOf q) (-19)) (literal (valuationOf q) (1422)) (countLit q [-18]) (countLit q [-19]) (count1421 q) 1 1 (meaningNeg18 q) (meaningNeg19 q) (meaning1422 q) hs
  change (! (valuationOf q 18)) = false ∨ (! (valuationOf q 19)) = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 19 = true ∨ valuation q 1422 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-17]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1421)) (literal (valuationOf q) (1423)) (countLit q [-17]) (countLit q [-18, -19]) (count1423 q) 1 (meaning1421 q) (meaning1423 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1423 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1424 = true := by
  have hs : count1423 q = (countLit q [-17]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -19])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1424)) (countLit q [-17]) (countLit q [-18, -19]) (count1423 q) 2 (meaning1422 q) (meaning1424 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1424 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1423 = true := by
  have hs : count1423 q = (countLit q [-17]) + (countLit q [-18, -19]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18, -19])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1423)) (countLit q [-17]) (countLit q [-18, -19]) (count1423 q) 1 (meaningNeg17 q) (meaning1423 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1423 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E169.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112169
