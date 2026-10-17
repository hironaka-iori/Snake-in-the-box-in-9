import E112171Semantics
import B112E171Inputs
namespace Snake9.Regrowth.E112171
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 23 = true ∨ valuationOf q 1391 = true := by
  have hs : count1390 q = (countLit q [-21]) + (countLit q [-23]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-23])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-23)) (literal (valuationOf q) (1391)) (countLit q [-21]) (countLit q [-23]) (count1390 q) 1 1 (meaningNeg21 q) (meaningNeg23 q) (meaning1391 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 23)) = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 23 = true ∨ valuation q 1391 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-26]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27])
  have hm := merge_right (literal (valuationOf q) (-27)) (literal (valuationOf q) (1392)) (countLit q [-26]) (countLit q [-27]) (count1392 q) 1 (meaningNeg27 q) (meaning1392 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1392 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-26]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1392)) (countLit q [-26]) (countLit q [-27]) (count1392 q) 1 (meaningNeg26 q) (meaning1392 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1392 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 27 = true ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-26]) + (countLit q [-27]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-27])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (-27)) (literal (valuationOf q) (1393)) (countLit q [-26]) (countLit q [-27]) (count1392 q) 1 1 (meaningNeg26 q) (meaningNeg27 q) (meaning1393 q) hs
  change (! (valuationOf q 26)) = false ∨ (! (valuationOf q 27)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 27 = true ∨ valuation q 1393 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1392 = false ∨ valuationOf q 1394 = true := by
  have hs : count1394 q = (countLit q [-21, -23]) + (countLit q [-26, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -27])
  have hm := merge_right (literal (valuationOf q) (1392)) (literal (valuationOf q) (1394)) (countLit q [-21, -23]) (countLit q [-26, -27]) (count1394 q) 1 (meaning1392 q) (meaning1394 q) hs
  change valuationOf q 1392 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1392 = false ∨ valuation q 1394 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1395 = true := by
  have hs : count1394 q = (countLit q [-21, -23]) + (countLit q [-26, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -27])
  have hm := merge_right (literal (valuationOf q) (1393)) (literal (valuationOf q) (1395)) (countLit q [-21, -23]) (countLit q [-26, -27]) (count1394 q) 2 (meaning1393 q) (meaning1395 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1395 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1394 = true := by
  have hs : count1394 q = (countLit q [-21, -23]) + (countLit q [-26, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -27])
  have hm := merge_left (literal (valuationOf q) (1390)) (literal (valuationOf q) (1394)) (countLit q [-21, -23]) (countLit q [-26, -27]) (count1394 q) 1 (meaning1390 q) (meaning1394 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1394 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1390 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1395 = true := by
  have hs : count1394 q = (countLit q [-21, -23]) + (countLit q [-26, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -27])
  have hm := merge_two (literal (valuationOf q) (1390)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1395)) (countLit q [-21, -23]) (countLit q [-26, -27]) (count1394 q) 1 1 (meaning1390 q) (meaning1392 q) (meaning1395 q) hs
  change valuationOf q 1390 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1390 = false ∨ valuation q 1392 = false ∨ valuation q 1395 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1391 = false ∨ valuationOf q 1395 = true := by
  have hs : count1394 q = (countLit q [-21, -23]) + (countLit q [-26, -27]) := List.countP_append (p := literal q) (l₁ := [-21, -23]) (l₂ := [-26, -27])
  have hm := merge_left (literal (valuationOf q) (1391)) (literal (valuationOf q) (1395)) (countLit q [-21, -23]) (countLit q [-26, -27]) (count1394 q) 2 (meaning1391 q) (meaning1395 q) hs
  change valuationOf q 1391 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1391 = false ∨ valuation q 1395 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -23, -26, -27])
  have hm := merge_right (literal (valuationOf q) (1394)) (literal (valuationOf q) (1398)) (countLit q [-17, -18, -19]) (countLit q [-21, -23, -26, -27]) (count1398 q) 1 (meaning1394 q) (meaning1398 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1398 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1399 = true := by
  have hs : count1398 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -23, -26, -27])
  have hm := merge_right (literal (valuationOf q) (1395)) (literal (valuationOf q) (1399)) (countLit q [-17, -18, -19]) (countLit q [-21, -23, -26, -27]) (count1398 q) 2 (meaning1395 q) (meaning1399 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1399 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1399 = true := by
  have hs : count1398 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1399)) (countLit q [-17, -18, -19]) (countLit q [-21, -23, -26, -27]) (count1398 q) 1 1 (meaning1387 q) (meaning1394 q) (meaning1399 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1394 = false ∨ valuation q 1399 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1400 = true := by
  have hs : count1398 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1395)) (literal (valuationOf q) (1400)) (countLit q [-17, -18, -19]) (countLit q [-21, -23, -26, -27]) (count1398 q) 1 2 (meaning1387 q) (meaning1395 q) (meaning1400 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1395 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1395 = false ∨ valuation q 1400 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1400 = true := by
  have hs : count1398 q = (countLit q [-17, -18, -19]) + (countLit q [-21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-17, -18, -19]) (l₂ := [-21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1400)) (countLit q [-17, -18, -19]) (countLit q [-21, -23, -26, -27]) (count1398 q) 2 1 (meaning1388 q) (meaning1394 q) (meaning1400 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1394 = false ∨ valuation q 1400 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1406 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_right (literal (valuationOf q) (1399)) (literal (valuationOf q) (1406)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 2 (meaning1399 q) (meaning1406 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1406 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1407 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1407)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 3 (meaning1400 q) (meaning1407 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1407 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1406 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1398)) (literal (valuationOf q) (1406)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 1 1 (meaning1378 q) (meaning1398 q) (meaning1406 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1398 = false ∨ valuation q 1406 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1407 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1407)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 1 2 (meaning1378 q) (meaning1399 q) (meaning1407 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1399 = false ∨ valuation q 1407 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1408 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1408)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 1 3 (meaning1378 q) (meaning1400 q) (meaning1408 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1400 = false ∨ valuation q 1408 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1407 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1398)) (literal (valuationOf q) (1407)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 2 1 (meaning1379 q) (meaning1398 q) (meaning1407 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1398 = false ∨ valuation q 1407 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1408 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1408)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 2 2 (meaning1379 q) (meaning1399 q) (meaning1408 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1399 = false ∨ valuation q 1408 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1409 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1379)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1409)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 2 3 (meaning1379 q) (meaning1400 q) (meaning1409 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1400 = false ∨ valuation q 1409 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1408 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1380)) (literal (valuationOf q) (1398)) (literal (valuationOf q) (1408)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 3 1 (meaning1380 q) (meaning1398 q) (meaning1408 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1408 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1398 = false ∨ valuation q 1408 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1409 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1380)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1409)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 3 2 (meaning1380 q) (meaning1399 q) (meaning1409 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1399 = false ∨ valuation q 1409 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1410 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1380)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1410)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 3 3 (meaning1380 q) (meaning1400 q) (meaning1410 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1400 = false ∨ valuation q 1410 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1409 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1398)) (literal (valuationOf q) (1409)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 4 1 (meaning1381 q) (meaning1398 q) (meaning1409 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1398 = false ∨ valuation q 1409 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1410 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1399)) (literal (valuationOf q) (1410)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 4 2 (meaning1381 q) (meaning1399 q) (meaning1410 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1399 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1399 = false ∨ valuation q 1410 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1410 = true := by
  have hs : count1405 q = (countLit q [-2, -4, -5, -8, -9, -11, -14]) + (countLit q [-17, -18, -19, -21, -23, -26, -27]) := List.countP_append (p := literal q) (l₁ := [-2, -4, -5, -8, -9, -11, -14]) (l₂ := [-17, -18, -19, -21, -23, -26, -27])
  have hm := merge_two (literal (valuationOf q) (1382)) (literal (valuationOf q) (1398)) (literal (valuationOf q) (1410)) (countLit q [-2, -4, -5, -8, -9, -11, -14]) (countLit q [-17, -18, -19, -21, -23, -26, -27]) (count1405 q) 5 1 (meaning1382 q) (meaning1398 q) (meaning1410 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1398 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1398 = false ∨ valuation q 1410 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 34 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_right (literal (valuationOf q) (-34)) (literal (valuationOf q) (1419)) (countLit q [-32]) (countLit q [-34]) (count1419 q) 1 (meaningNeg34 q) (meaning1419 q) hs
  change (! (valuationOf q 34)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 34 = true ∨ valuation q 1419 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_left (literal (valuationOf q) (-32)) (literal (valuationOf q) (1419)) (countLit q [-32]) (countLit q [-34]) (count1419 q) 1 (meaningNeg32 q) (meaning1419 q) hs
  change (! (valuationOf q 32)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 1419 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 32 = true ∨ valuationOf q 34 = true ∨ valuationOf q 1420 = true := by
  have hs : count1419 q = (countLit q [-32]) + (countLit q [-34]) := List.countP_append (p := literal q) (l₁ := [-32]) (l₂ := [-34])
  have hm := merge_two (literal (valuationOf q) (-32)) (literal (valuationOf q) (-34)) (literal (valuationOf q) (1420)) (countLit q [-32]) (countLit q [-34]) (count1419 q) 1 1 (meaningNeg32 q) (meaningNeg34 q) (meaning1420 q) hs
  change (! (valuationOf q 32)) = false ∨ (! (valuationOf q 34)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 32 = true ∨ valuation q 34 = true ∨ valuation q 1420 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-30]) + (countLit q [-32, -34]) := List.countP_append (p := literal q) (l₁ := [-30]) (l₂ := [-32, -34])
  have hm := merge_right (literal (valuationOf q) (1419)) (literal (valuationOf q) (1421)) (countLit q [-30]) (countLit q [-32, -34]) (count1421 q) 1 (meaning1419 q) (meaning1421 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1421 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E171.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112171
