import E112179Semantics
import B112E179Inputs
namespace Snake9.Regrowth.E112179
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1392)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 1 1 (meaning1383 q) (meaning1388 q) (meaning1392 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1388 = false ∨ valuation q 1392 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true := by
  have hs : count1391 q = (countLit q [-79, -80, -81]) + (countLit q [-85, -87, -90]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81]) (l₂ := [-85, -87, -90])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1393)) (countLit q [-79, -80, -81]) (countLit q [-85, -87, -90]) (count1391 q) 1 2 (meaning1383 q) (meaning1389 q) (meaning1393 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1389 = false ∨ valuation q 1393 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-93]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95])
  have hm := merge_right (literal (valuationOf q) (-95)) (literal (valuationOf q) (1397)) (countLit q [-93]) (countLit q [-95]) (count1397 q) 1 (meaningNeg95 q) (meaning1397 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1397 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1397 = true := by
  have hs : count1397 q = (countLit q [-93]) + (countLit q [-95]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-95])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1397)) (countLit q [-93]) (countLit q [-95]) (count1397 q) 1 (meaningNeg93 q) (meaning1397 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1397 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1397 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 1397 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-92]) + (countLit q [-93, -95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -95])
  have hm := merge_right (literal (valuationOf q) (1397)) (literal (valuationOf q) (1399)) (countLit q [-92]) (countLit q [-93, -95]) (count1399 q) 1 (meaning1397 q) (meaning1399 q) hs
  change valuationOf q 1397 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 1397 = false ∨ valuation q 1399 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-92]) + (countLit q [-93, -95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -95])
  have hm := merge_left (literal (valuationOf q) (-92)) (literal (valuationOf q) (1399)) (countLit q [-92]) (countLit q [-93, -95]) (count1399 q) 1 (meaningNeg92 q) (meaning1399 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1399 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-92]) + (countLit q [-93, -95]) := List.countP_append (p := literal q) (l₁ := [-92]) (l₂ := [-93, -95])
  have hm := merge_two (literal (valuationOf q) (-92)) (literal (valuationOf q) (1397)) (literal (valuationOf q) (1400)) (countLit q [-92]) (countLit q [-93, -95]) (count1399 q) 1 1 (meaningNeg92 q) (meaning1397 q) (meaning1400 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1397 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1397 = false ∨ valuation q 1400 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 100 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_right (literal (valuationOf q) (-100)) (literal (valuationOf q) (1402)) (countLit q [-99]) (countLit q [-100]) (count1402 q) 1 (meaningNeg100 q) (meaning1402 q) hs
  change (! (valuationOf q 100)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 100 = true ∨ valuation q 1402 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 99 = true ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-99]) + (countLit q [-100]) := List.countP_append (p := literal q) (l₁ := [-99]) (l₂ := [-100])
  have hm := merge_left (literal (valuationOf q) (-99)) (literal (valuationOf q) (1402)) (countLit q [-99]) (countLit q [-100]) (count1402 q) 1 (meaningNeg99 q) (meaning1402 q) hs
  change (! (valuationOf q 99)) = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 99 = true ∨ valuation q 1402 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1404 = true := by
  have hs : count1404 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1404)) (countLit q [-101]) (countLit q [-102]) (count1404 q) 1 (meaningNeg102 q) (meaning1404 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1404 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1404 = true := by
  have hs : count1404 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1404)) (countLit q [-101]) (countLit q [-102]) (count1404 q) 1 (meaningNeg101 q) (meaning1404 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1404 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-99, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-101, -102])
  have hm := merge_right (literal (valuationOf q) (1404)) (literal (valuationOf q) (1406)) (countLit q [-99, -100]) (countLit q [-101, -102]) (count1406 q) 1 (meaning1404 q) (meaning1406 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1406 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-99, -100]) + (countLit q [-101, -102]) := List.countP_append (p := literal q) (l₁ := [-99, -100]) (l₂ := [-101, -102])
  have hm := merge_left (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-99, -100]) (countLit q [-101, -102]) (count1406 q) 1 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1406 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_right (literal (valuationOf q) (1406)) (literal (valuationOf q) (1410)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 1 (meaning1406 q) (meaning1410 q) hs
  change valuationOf q 1406 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1406 = false ∨ valuation q 1410 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1410 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1399)) (literal (valuationOf q) (1410)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 1 (meaning1399 q) (meaning1410 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1410 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1411)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 1 1 (meaning1399 q) (meaning1406 q) (meaning1411 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1406 = false ∨ valuation q 1411 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1400)) (literal (valuationOf q) (1411)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 2 (meaning1400 q) (meaning1411 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1411 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1418)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 1 1 (meaning1391 q) (meaning1410 q) (meaning1418 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1410 = false ∨ valuation q 1418 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1419)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 1 2 (meaning1391 q) (meaning1411 q) (meaning1419 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1411 = false ∨ valuation q 1419 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1419)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 2 1 (meaning1392 q) (meaning1410 q) (meaning1419 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1410 = false ∨ valuation q 1419 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1420)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 2 2 (meaning1392 q) (meaning1411 q) (meaning1420 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1411 = false ∨ valuation q 1420 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1393)) (literal (valuationOf q) (1419)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 3 (meaning1393 q) (meaning1419 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1419 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1420)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 3 1 (meaning1393 q) (meaning1410 q) (meaning1420 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1410 = false ∨ valuation q 1420 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1429)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 1 2 (meaning1371 q) (meaning1418 q) (meaning1429 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1418 = false ∨ valuation q 1429 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1430)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 1 3 (meaning1371 q) (meaning1419 q) (meaning1430 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1419 = false ∨ valuation q 1430 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1431)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 1 4 (meaning1371 q) (meaning1420 q) (meaning1431 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1420 = false ∨ valuation q 1431 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1430)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 2 (meaning1372 q) (meaning1418 q) (meaning1430 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1418 = false ∨ valuation q 1430 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1431)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 3 (meaning1372 q) (meaning1419 q) (meaning1431 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1419 = false ∨ valuation q 1431 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1432)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 4 (meaning1372 q) (meaning1420 q) (meaning1432 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1420 = false ∨ valuation q 1432 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1431)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 2 (meaning1373 q) (meaning1418 q) (meaning1431 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1418 = false ∨ valuation q 1431 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1432)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 3 (meaning1373 q) (meaning1419 q) (meaning1432 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1419 = false ∨ valuation q 1432 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1432)) (countLit q [-53, -54, -58, -60, -61, -63, -67, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 4 2 (meaning1374 q) (meaning1418 q) (meaning1432 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1418 = false ∨ valuation q 1432 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E179.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112179
