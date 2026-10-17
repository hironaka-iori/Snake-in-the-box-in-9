import E112225Semantics
import B112E225Inputs
namespace Snake9.Regrowth.E112225
noncomputable section
local instance blockDec14 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause449 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-77, -81, -83]) + (countLit q [-85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83]) (l₂ := [-85, -87, -88])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1393)) (countLit q [-77, -81, -83]) (countLit q [-85, -87, -88]) (count1391 q) 2 1 (meaning1384 q) (meaning1388 q) (meaning1393 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause449 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = false ∨ valuation q 1393 = true := counterClause449 (baseVal q)

theorem counterClause450 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-77, -81, -83]) + (countLit q [-85, -87, -88]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83]) (l₂ := [-85, -87, -88])
  have hm := merge_left (literal (valuationOf q) (1385)) (literal (valuationOf q) (1393)) (countLit q [-77, -81, -83]) (countLit q [-85, -87, -88]) (count1391 q) 3 (meaning1385 q) (meaning1393 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause450 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1393 = true := counterClause450 (baseVal q)

theorem counterClause451 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_right (literal (valuationOf q) (-96)) (literal (valuationOf q) (1397)) (countLit q [-92]) (countLit q [-96]) (count1397 q) 1 (meaningNeg96 q) (meaning1397 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause451 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1397 = true := counterClause451 (baseVal q)

theorem counterClause452 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1397)) (countLit q [-92]) (countLit q [-96]) (count1397 q) 1 (meaningNeg92 q) (meaning1397 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause452 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1397 = true := counterClause452 (baseVal q)

theorem counterClause453 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 96 = true ∨ valuationOf q 1398 = true := by
  have hs : count1397 q = (countLit q [-92]) + (countLit q [-96]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-96])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (-96)) (literal (valuationOf q) (1398)) (countLit q [-92]) (countLit q [-96]) (count1397 q) 1 1 (meaningNeg92 q) (meaningNeg96 q) (meaning1398 q) hs
  change (! (valuationOf q 92)) = false ∨ (! (valuationOf q 96)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause453 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 96 = true ∨ valuation q 1398 = true := counterClause453 (baseVal q)

theorem counterClause454 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_right (literal (valuationOf q) (1397)) (literal (valuationOf q) (1399)) (countLit q [-91]) (countLit q [-92, -96]) (count1399 q) 1 (meaning1397 q) (meaning1399 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause454 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1399 = true := counterClause454 (baseVal q)

theorem counterClause455 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_right (literal (valuationOf q) (1398)) (literal (valuationOf q) (1400)) (countLit q [-91]) (countLit q [-92, -96]) (count1399 q) 2 (meaning1398 q) (meaning1400 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause455 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1400 = true := counterClause455 (baseVal q)

theorem counterClause456 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_left (literal (valuationOf q) (-91)) (literal (valuationOf q) (1399)) (countLit q [-91]) (countLit q [-92, -96]) (count1399 q) 1 (meaningNeg91 q) (meaning1399 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause456 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1399 = true := counterClause456 (baseVal q)

theorem counterClause457 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1400)) (countLit q [-91]) (countLit q [-92, -96]) (count1399 q) 1 1 (meaningNeg91 q) (meaning1397 q) (meaning1400 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause457 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1397 = false ∨ valuation q 1400 = true := counterClause457 (baseVal q)

theorem counterClause458 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1398 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-91]) + (countLit q [-92, -96]) := List.countP_append (p := literal q) (l₁ := [-91]) (l₂ := [-92, -96])
  have hm := merge_two (literal (valuationOf q) (-91)) (literal (valuationOf q) (1398)) (literal (valuationOf q) (1401)) (countLit q [-91]) (countLit q [-92, -96]) (count1399 q) 1 2 (meaningNeg91 q) (meaning1398 q) (meaning1401 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause458 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1398 = false ∨ valuation q 1401 = true := counterClause458 (baseVal q)

theorem counterClause459 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_right (literal (valuationOf q) (-99)) (literal (valuationOf q) (1402)) (countLit q [-98]) (countLit q [-99]) (count1402 q) 1 (meaningNeg99 q) (meaning1402 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause459 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1402 = true := counterClause459 (baseVal q)

theorem counterClause460 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_left (literal (valuationOf q) (-98)) (literal (valuationOf q) (1402)) (countLit q [-98]) (countLit q [-99]) (count1402 q) 1 (meaningNeg98 q) (meaning1402 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause460 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1402 = true := counterClause460 (baseVal q)

theorem counterClause461 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 99 = true ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-98]) + (countLit q [-99]) := List.countP_append (p := literal q) (l₁ := [-98]) (l₂ := [-99])
  have hm := merge_two (literal (valuationOf q) (-98)) (literal (valuationOf q) (-99)) (literal (valuationOf q) (1403)) (countLit q [-98]) (countLit q [-99]) (count1402 q) 1 1 (meaningNeg98 q) (meaningNeg99 q) (meaning1403 q) hs
  change (! (valuationOf q 98)) = false ∨ (! (valuationOf q 99)) = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause461 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 99 = true ∨ valuation q 1403 = true := counterClause461 (baseVal q)

theorem counterClause462 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1404 = true := by
  have hs : count1404 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_right (literal (valuationOf q) (-103)) (literal (valuationOf q) (1404)) (countLit q [-101]) (countLit q [-103]) (count1404 q) 1 (meaningNeg103 q) (meaning1404 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause462 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1404 = true := counterClause462 (baseVal q)

theorem counterClause463 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1404 = true := by
  have hs : count1404 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1404)) (countLit q [-101]) (countLit q [-103]) (count1404 q) 1 (meaningNeg101 q) (meaning1404 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause463 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1404 = true := counterClause463 (baseVal q)

theorem counterClause464 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 103 = true ∨ valuationOf q 1405 = true := by
  have hs : count1404 q = (countLit q [-101]) + (countLit q [-103]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-103])
  have hm := merge_two (literal (valuationOf q) (-101)) (literal (valuationOf q) (-103)) (literal (valuationOf q) (1405)) (countLit q [-101]) (countLit q [-103]) (count1404 q) 1 1 (meaningNeg101 q) (meaningNeg103 q) (meaning1405 q) hs
  change (! (valuationOf q 101)) = false ∨ (! (valuationOf q 103)) = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause464 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 103 = true ∨ valuation q 1405 = true := counterClause464 (baseVal q)

theorem counterClause465 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-98, -99]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-101, -103])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1406)) (countLit q [-98, -99]) (countLit q [-101, -103]) (count1406 q) 1 (meaning1404 q) (meaning1406 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause465 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1406 = true := counterClause465 (baseVal q)

theorem counterClause466 (q : Nat → Bool) : valuationOf q 1405 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-98, -99]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-101, -103])
  have hm := merge_right (literal (valuationOf q) (1405)) (literal (valuationOf q) (1407)) (countLit q [-98, -99]) (countLit q [-101, -103]) (count1406 q) 2 (meaning1405 q) (meaning1407 q) hs
  change valuationOf q 1405 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause466 (q : Snake 81) (h : Conditions q) : valuation q 1405 = false ∨ valuation q 1407 = true := counterClause466 (baseVal q)

theorem counterClause467 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-98, -99]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-101, -103])
  have hm := merge_left (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-98, -99]) (countLit q [-101, -103]) (count1406 q) 1 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause467 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause467 (baseVal q)

theorem counterClause468 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-98, -99]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-101, -103])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1407)) (countLit q [-98, -99]) (countLit q [-101, -103]) (count1406 q) 1 1 (meaning1402 q) (meaning1404 q) (meaning1407 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause468 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1404 = false ∨ valuation q 1407 = true := counterClause468 (baseVal q)

theorem counterClause469 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-98, -99]) + (countLit q [-101, -103]) := List.countP_append (p := literal q) (l₁ := [-98, -99]) (l₂ := [-101, -103])
  have hm := merge_left (literal (valuationOf q) (1403)) (literal (valuationOf q) (1407)) (countLit q [-98, -99]) (countLit q [-101, -103]) (count1406 q) 2 (meaning1403 q) (meaning1407 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause469 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1407 = true := counterClause469 (baseVal q)

theorem counterClause470 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1406)) (literal (valuationOf q) (1410)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 1 (meaning1406 q) (meaning1410 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause470 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1410 = true := counterClause470 (baseVal q)

theorem counterClause471 (q : Nat → Bool) : valuationOf q 1407 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_right (literal (valuationOf q) (1407)) (literal (valuationOf q) (1411)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 2 (meaning1407 q) (meaning1411 q) hs
  change valuationOf q 1407 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause471 (q : Snake 81) (h : Conditions q) : valuation q 1407 = false ∨ valuation q 1411 = true := counterClause471 (baseVal q)

theorem counterClause472 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_left (literal (valuationOf q) (1399)) (literal (valuationOf q) (1410)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 1 (meaning1399 q) (meaning1410 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause472 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1410 = true := counterClause472 (baseVal q)

theorem counterClause473 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1411)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 1 1 (meaning1399 q) (meaning1406 q) (meaning1411 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause473 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1406 = false ∨ valuation q 1411 = true := counterClause473 (baseVal q)

theorem counterClause474 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1412)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 1 2 (meaning1399 q) (meaning1407 q) (meaning1412 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause474 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1407 = false ∨ valuation q 1412 = true := counterClause474 (baseVal q)

theorem counterClause475 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_left (literal (valuationOf q) (1400)) (literal (valuationOf q) (1411)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 2 (meaning1400 q) (meaning1411 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause475 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1411 = true := counterClause475 (baseVal q)

theorem counterClause476 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1412)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 2 1 (meaning1400 q) (meaning1406 q) (meaning1412 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause476 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1406 = false ∨ valuation q 1412 = true := counterClause476 (baseVal q)

theorem counterClause477 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1413 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1413)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 2 2 (meaning1400 q) (meaning1407 q) (meaning1413 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause477 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1407 = false ∨ valuation q 1413 = true := counterClause477 (baseVal q)

theorem counterClause478 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_left (literal (valuationOf q) (1401)) (literal (valuationOf q) (1412)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 3 (meaning1401 q) (meaning1412 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause478 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1412 = true := counterClause478 (baseVal q)

theorem counterClause479 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1413 = true := by
  have hs : count1410 q = (countLit q [-91, -92, -96]) + (countLit q [-98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-91, -92, -96]) (l₂ := [-98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1413)) (countLit q [-91, -92, -96]) (countLit q [-98, -99, -101, -103]) (count1410 q) 3 1 (meaning1401 q) (meaning1406 q) (meaning1413 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause479 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1406 = false ∨ valuation q 1413 = true := counterClause479 (baseVal q)

theorem counterClause480 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-77, -81, -83, -85, -87, -88]) + (countLit q [-91, -92, -96, -98, -99, -101, -103]) := List.countP_append (p := literal q) (l₁ := [-77, -81, -83, -85, -87, -88]) (l₂ := [-91, -92, -96, -98, -99, -101, -103])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1418)) (countLit q [-77, -81, -83, -85, -87, -88]) (countLit q [-91, -92, -96, -98, -99, -101, -103]) (count1417 q) 1 1 (meaning1391 q) (meaning1410 q) (meaning1418 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause480 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1410 = false ∨ valuation q 1418 = true := counterClause480 (baseVal q)

theorem block14 (q : Snake 81) (h : Conditions q) : B112E225.Block14 (valuation q) :=
  ⟨clause449 q h, clause450 q h, clause451 q h, clause452 q h, clause453 q h, clause454 q h, clause455 q h, clause456 q h, clause457 q h, clause458 q h, clause459 q h, clause460 q h, clause461 q h, clause462 q h, clause463 q h, clause464 q h, clause465 q h, clause466 q h, clause467 q h, clause468 q h, clause469 q h, clause470 q h, clause471 q h, clause472 q h, clause473 q h, clause474 q h, clause475 q h, clause476 q h, clause477 q h, clause478 q h, clause479 q h, clause480 q h⟩

end
end Snake9.Regrowth.E112225
