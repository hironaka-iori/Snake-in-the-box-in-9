import E112175Semantics
import B112E175Inputs
namespace Snake9.Regrowth.E112175
noncomputable section
local instance blockDec23 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause737 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1411)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 1 1 (meaning1399 q) (meaning1406 q) (meaning1411 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause737 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1406 = false ∨ valuation q 1411 = true := counterClause737 (baseVal q)

theorem counterClause738 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1407)) (literal (valuationOf q) (1412)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 1 2 (meaning1399 q) (meaning1407 q) (meaning1412 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1407 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause738 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1407 = false ∨ valuation q 1412 = true := counterClause738 (baseVal q)

theorem counterClause739 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1411 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1400)) (literal (valuationOf q) (1411)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 2 (meaning1400 q) (meaning1411 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause739 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1411 = true := counterClause739 (baseVal q)

theorem counterClause740 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1412 = true := by
  have hs : count1410 q = (countLit q [-92, -93, -95]) + (countLit q [-99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-92, -93, -95]) (l₂ := [-99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1406)) (literal (valuationOf q) (1412)) (countLit q [-92, -93, -95]) (countLit q [-99, -100, -101, -102]) (count1410 q) 2 1 (meaning1400 q) (meaning1406 q) (meaning1412 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1406 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause740 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1406 = false ∨ valuation q 1412 = true := counterClause740 (baseVal q)

theorem counterClause741 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1391)) (literal (valuationOf q) (1417)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 1 (meaning1391 q) (meaning1417 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause741 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1417 = true := counterClause741 (baseVal q)

theorem counterClause742 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1418)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 1 1 (meaning1391 q) (meaning1410 q) (meaning1418 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause742 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1410 = false ∨ valuation q 1418 = true := counterClause742 (baseVal q)

theorem counterClause743 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1419)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 1 2 (meaning1391 q) (meaning1411 q) (meaning1419 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause743 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1411 = false ∨ valuation q 1419 = true := counterClause743 (baseVal q)

theorem counterClause744 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1391)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1420)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 1 3 (meaning1391 q) (meaning1412 q) (meaning1420 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause744 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1412 = false ∨ valuation q 1420 = true := counterClause744 (baseVal q)

theorem counterClause745 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1392)) (literal (valuationOf q) (1418)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 2 (meaning1392 q) (meaning1418 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause745 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1418 = true := counterClause745 (baseVal q)

theorem counterClause746 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1419)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 2 1 (meaning1392 q) (meaning1410 q) (meaning1419 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause746 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1410 = false ∨ valuation q 1419 = true := counterClause746 (baseVal q)

theorem counterClause747 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1392)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1420)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 2 2 (meaning1392 q) (meaning1411 q) (meaning1420 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause747 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1411 = false ∨ valuation q 1420 = true := counterClause747 (baseVal q)

theorem counterClause748 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1420)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 3 1 (meaning1393 q) (meaning1410 q) (meaning1420 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause748 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1410 = false ∨ valuation q 1420 = true := counterClause748 (baseVal q)

theorem counterClause749 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1421 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1393)) (literal (valuationOf q) (1411)) (literal (valuationOf q) (1421)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 3 2 (meaning1393 q) (meaning1411 q) (meaning1421 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1411 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause749 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1411 = false ∨ valuation q 1421 = true := counterClause749 (baseVal q)

theorem counterClause750 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1420 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_left (literal (valuationOf q) (1394)) (literal (valuationOf q) (1420)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 4 (meaning1394 q) (meaning1420 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause750 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1420 = true := counterClause750 (baseVal q)

theorem counterClause751 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1421 = true := by
  have hs : count1417 q = (countLit q [-79, -80, -81, -85, -87, -90]) + (countLit q [-92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-79, -80, -81, -85, -87, -90]) (l₂ := [-92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1394)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1421)) (countLit q [-79, -80, -81, -85, -87, -90]) (countLit q [-92, -93, -95, -99, -100, -101, -102]) (count1417 q) 4 1 (meaning1394 q) (meaning1410 q) (meaning1421 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause751 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1410 = false ∨ valuation q 1421 = true := counterClause751 (baseVal q)

theorem counterClause752 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1429)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 1 2 (meaning1371 q) (meaning1418 q) (meaning1429 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause752 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1418 = false ∨ valuation q 1429 = true := counterClause752 (baseVal q)

theorem counterClause753 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1430)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 1 3 (meaning1371 q) (meaning1419 q) (meaning1430 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause753 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1419 = false ∨ valuation q 1430 = true := counterClause753 (baseVal q)

theorem counterClause754 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1431)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 1 4 (meaning1371 q) (meaning1420 q) (meaning1431 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause754 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1420 = false ∨ valuation q 1431 = true := counterClause754 (baseVal q)

theorem counterClause755 (q : Nat → Bool) : valuationOf q 1371 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1371)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1432)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 1 5 (meaning1371 q) (meaning1421 q) (meaning1432 q) hs
  change valuationOf q 1371 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause755 (q : Snake 81) (h : Conditions q) : valuation q 1371 = false ∨ valuation q 1421 = false ∨ valuation q 1432 = true := counterClause755 (baseVal q)

theorem counterClause756 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1429 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1429)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 1 (meaning1372 q) (meaning1417 q) (meaning1429 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause756 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1417 = false ∨ valuation q 1429 = true := counterClause756 (baseVal q)

theorem counterClause757 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1430)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 2 (meaning1372 q) (meaning1418 q) (meaning1430 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause757 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1418 = false ∨ valuation q 1430 = true := counterClause757 (baseVal q)

theorem counterClause758 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1431)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 3 (meaning1372 q) (meaning1419 q) (meaning1431 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause758 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1419 = false ∨ valuation q 1431 = true := counterClause758 (baseVal q)

theorem counterClause759 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1432)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 4 (meaning1372 q) (meaning1420 q) (meaning1432 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause759 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1420 = false ∨ valuation q 1432 = true := counterClause759 (baseVal q)

theorem counterClause760 (q : Nat → Bool) : valuationOf q 1372 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1372)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1433)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 2 5 (meaning1372 q) (meaning1421 q) (meaning1433 q) hs
  change valuationOf q 1372 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause760 (q : Snake 81) (h : Conditions q) : valuation q 1372 = false ∨ valuation q 1421 = false ∨ valuation q 1433 = true := counterClause760 (baseVal q)

theorem counterClause761 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1430 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1430)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 1 (meaning1373 q) (meaning1417 q) (meaning1430 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1430 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause761 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1417 = false ∨ valuation q 1430 = true := counterClause761 (baseVal q)

theorem counterClause762 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1431)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 2 (meaning1373 q) (meaning1418 q) (meaning1431 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause762 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1418 = false ∨ valuation q 1431 = true := counterClause762 (baseVal q)

theorem counterClause763 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1432)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 3 (meaning1373 q) (meaning1419 q) (meaning1432 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause763 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1419 = false ∨ valuation q 1432 = true := counterClause763 (baseVal q)

theorem counterClause764 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1433)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 4 (meaning1373 q) (meaning1420 q) (meaning1433 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause764 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1420 = false ∨ valuation q 1433 = true := counterClause764 (baseVal q)

theorem counterClause765 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1434 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1434)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 3 5 (meaning1373 q) (meaning1421 q) (meaning1434 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause765 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1421 = false ∨ valuation q 1434 = true := counterClause765 (baseVal q)

theorem counterClause766 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1431 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1417)) (literal (valuationOf q) (1431)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 4 1 (meaning1374 q) (meaning1417 q) (meaning1431 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1417 = false ∨ valuationOf q 1431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause766 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1417 = false ∨ valuation q 1431 = true := counterClause766 (baseVal q)

theorem counterClause767 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1418)) (literal (valuationOf q) (1432)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 4 2 (meaning1374 q) (meaning1418 q) (meaning1432 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1418 = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause767 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1418 = false ∨ valuation q 1432 = true := counterClause767 (baseVal q)

theorem counterClause768 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1433 = true := by
  have hs : count1427 q = (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) + (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (l₂ := [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1433)) (countLit q [-54, -55, -59, -61, -62, -64, -68, -69, -70, -71, -75, -77]) (countLit q [-79, -80, -81, -85, -87, -90, -92, -93, -95, -99, -100, -101, -102]) (count1427 q) 4 3 (meaning1374 q) (meaning1419 q) (meaning1433 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause768 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1419 = false ∨ valuation q 1433 = true := counterClause768 (baseVal q)

theorem block23 (q : Snake 81) (h : Conditions q) : B112E175.Block23 (valuation q) :=
  ⟨clause737 q h, clause738 q h, clause739 q h, clause740 q h, clause741 q h, clause742 q h, clause743 q h, clause744 q h, clause745 q h, clause746 q h, clause747 q h, clause748 q h, clause749 q h, clause750 q h, clause751 q h, clause752 q h, clause753 q h, clause754 q h, clause755 q h, clause756 q h, clause757 q h, clause758 q h, clause759 q h, clause760 q h, clause761 q h, clause762 q h, clause763 q h, clause764 q h, clause765 q h, clause766 q h, clause767 q h, clause768 q h⟩

end
end Snake9.Regrowth.E112175
