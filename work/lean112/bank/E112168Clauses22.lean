import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec22 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause705 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_left (literal (valuationOf q) (1376)) (literal (valuationOf q) (1387)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 2 (meaning1376 q) (meaning1387 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause705 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1387 = true := counterClause705 (baseVal q)

theorem counterClause706 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1388 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1388)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 2 1 (meaning1376 q) (meaning1382 q) (meaning1388 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause706 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1382 = false ∨ valuation q 1388 = true := counterClause706 (baseVal q)

theorem counterClause707 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1389 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1389)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 2 2 (meaning1376 q) (meaning1383 q) (meaning1389 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause707 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1383 = false ∨ valuation q 1389 = true := counterClause707 (baseVal q)

theorem counterClause708 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1390 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1390)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 2 3 (meaning1376 q) (meaning1384 q) (meaning1390 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause708 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1384 = false ∨ valuation q 1390 = true := counterClause708 (baseVal q)

theorem counterClause709 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1391 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1391)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 2 4 (meaning1376 q) (meaning1385 q) (meaning1391 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause709 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1385 = false ∨ valuation q 1391 = true := counterClause709 (baseVal q)

theorem counterClause710 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1388 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_left (literal (valuationOf q) (1377)) (literal (valuationOf q) (1388)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 3 (meaning1377 q) (meaning1388 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause710 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1388 = true := counterClause710 (baseVal q)

theorem counterClause711 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1389 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1377)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1389)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 3 1 (meaning1377 q) (meaning1382 q) (meaning1389 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause711 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1382 = false ∨ valuation q 1389 = true := counterClause711 (baseVal q)

theorem counterClause712 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1390 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1377)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1390)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 3 2 (meaning1377 q) (meaning1383 q) (meaning1390 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause712 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1383 = false ∨ valuation q 1390 = true := counterClause712 (baseVal q)

theorem counterClause713 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1391 = true := by
  have hs : count1386 q = (countLit q [-2, -3, -5]) + (countLit q [-8, -10, -11, -12]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -5]) (l₂ := [-8, -10, -11, -12])
  have hm := merge_two (literal (valuationOf q) (1377)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1391)) (countLit q [-2, -3, -5]) (countLit q [-8, -10, -11, -12]) (count1386 q) 3 3 (meaning1377 q) (meaning1384 q) (meaning1391 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1391 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause713 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1384 = false ∨ valuation q 1391 = true := counterClause713 (baseVal q)

theorem counterClause714 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1393)) (countLit q [-17]) (countLit q [-18]) (count1393 q) 1 (meaningNeg18 q) (meaning1393 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause714 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1393 = true := counterClause714 (baseVal q)

theorem counterClause715 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1393 = true := by
  have hs : count1393 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1393)) (countLit q [-17]) (countLit q [-18]) (count1393 q) 1 (meaningNeg17 q) (meaning1393 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause715 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1393 = true := counterClause715 (baseVal q)

theorem counterClause716 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 18 = true ∨ valuationOf q 1394 = true := by
  have hs : count1393 q = (countLit q [-17]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (1394)) (countLit q [-17]) (countLit q [-18]) (count1393 q) 1 1 (meaningNeg17 q) (meaningNeg18 q) (meaning1394 q) hs
  change (! (valuationOf q 17)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause716 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 18 = true ∨ valuation q 1394 = true := counterClause716 (baseVal q)

theorem counterClause717 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_right (literal (valuationOf q) (1393)) (literal (valuationOf q) (1395)) (countLit q [-15]) (countLit q [-17, -18]) (count1395 q) 1 (meaning1393 q) (meaning1395 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause717 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1395 = true := counterClause717 (baseVal q)

theorem counterClause718 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_right (literal (valuationOf q) (1394)) (literal (valuationOf q) (1396)) (countLit q [-15]) (countLit q [-17, -18]) (count1395 q) 2 (meaning1394 q) (meaning1396 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause718 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1396 = true := counterClause718 (baseVal q)

theorem counterClause719 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1395 = true := by
  have hs : count1395 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_left (literal (valuationOf q) (-15)) (literal (valuationOf q) (1395)) (countLit q [-15]) (countLit q [-17, -18]) (count1395 q) 1 (meaningNeg15 q) (meaning1395 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause719 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1395 = true := counterClause719 (baseVal q)

theorem counterClause720 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true := by
  have hs : count1395 q = (countLit q [-15]) + (countLit q [-17, -18]) := List.countP_append (p := literal q) (l₁ := [-15]) (l₂ := [-17, -18])
  have hm := merge_two (literal (valuationOf q) (-15)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1396)) (countLit q [-15]) (countLit q [-17, -18]) (count1395 q) 1 1 (meaningNeg15 q) (meaning1393 q) (meaning1396 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1396 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause720 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1393 = false ∨ valuation q 1396 = true := counterClause720 (baseVal q)

theorem counterClause721 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1398)) (countLit q [-21]) (countLit q [-24]) (count1398 q) 1 (meaningNeg24 q) (meaning1398 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause721 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1398 = true := counterClause721 (baseVal q)

theorem counterClause722 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1398 = true := by
  have hs : count1398 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1398)) (countLit q [-21]) (countLit q [-24]) (count1398 q) 1 (meaningNeg21 q) (meaning1398 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause722 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1398 = true := counterClause722 (baseVal q)

theorem counterClause723 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1399 = true := by
  have hs : count1398 q = (countLit q [-21]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1399)) (countLit q [-21]) (countLit q [-24]) (count1398 q) 1 1 (meaningNeg21 q) (meaningNeg24 q) (meaning1399 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause723 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 24 = true ∨ valuation q 1399 = true := counterClause723 (baseVal q)

theorem counterClause724 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1400 = true := by
  have hs : count1400 q = (countLit q [-26]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1400)) (countLit q [-26]) (countLit q [-29]) (count1400 q) 1 (meaningNeg29 q) (meaning1400 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause724 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1400 = true := counterClause724 (baseVal q)

theorem counterClause725 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1400 = true := by
  have hs : count1400 q = (countLit q [-26]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-26)) (literal (valuationOf q) (1400)) (countLit q [-26]) (countLit q [-29]) (count1400 q) 1 (meaningNeg26 q) (meaning1400 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause725 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1400 = true := counterClause725 (baseVal q)

theorem counterClause726 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 29 = true ∨ valuationOf q 1401 = true := by
  have hs : count1400 q = (countLit q [-26]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-26]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-26)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (1401)) (countLit q [-26]) (countLit q [-29]) (count1400 q) 1 1 (meaningNeg26 q) (meaningNeg29 q) (meaning1401 q) hs
  change (! (valuationOf q 26)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause726 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 29 = true ∨ valuation q 1401 = true := counterClause726 (baseVal q)

theorem counterClause727 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-21, -24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-26, -29])
  have hm := merge_right (literal (valuationOf q) (1400)) (literal (valuationOf q) (1402)) (countLit q [-21, -24]) (countLit q [-26, -29]) (count1402 q) 1 (meaning1400 q) (meaning1402 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause727 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1402 = true := counterClause727 (baseVal q)

theorem counterClause728 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-21, -24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-26, -29])
  have hm := merge_right (literal (valuationOf q) (1401)) (literal (valuationOf q) (1403)) (countLit q [-21, -24]) (countLit q [-26, -29]) (count1402 q) 2 (meaning1401 q) (meaning1403 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause728 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1403 = true := counterClause728 (baseVal q)

theorem counterClause729 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1402 = true := by
  have hs : count1402 q = (countLit q [-21, -24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-26, -29])
  have hm := merge_left (literal (valuationOf q) (1398)) (literal (valuationOf q) (1402)) (countLit q [-21, -24]) (countLit q [-26, -29]) (count1402 q) 1 (meaning1398 q) (meaning1402 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause729 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1402 = true := counterClause729 (baseVal q)

theorem counterClause730 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-21, -24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-26, -29])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1403)) (countLit q [-21, -24]) (countLit q [-26, -29]) (count1402 q) 1 1 (meaning1398 q) (meaning1400 q) (meaning1403 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause730 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1400 = false ∨ valuation q 1403 = true := counterClause730 (baseVal q)

theorem counterClause731 (q : Nat → Bool) : valuationOf q 1398 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true := by
  have hs : count1402 q = (countLit q [-21, -24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-26, -29])
  have hm := merge_two (literal (valuationOf q) (1398)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1404)) (countLit q [-21, -24]) (countLit q [-26, -29]) (count1402 q) 1 2 (meaning1398 q) (meaning1401 q) (meaning1404 q) hs
  change valuationOf q 1398 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause731 (q : Snake 81) (h : Conditions q) : valuation q 1398 = false ∨ valuation q 1401 = false ∨ valuation q 1404 = true := counterClause731 (baseVal q)

theorem counterClause732 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1403 = true := by
  have hs : count1402 q = (countLit q [-21, -24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-26, -29])
  have hm := merge_left (literal (valuationOf q) (1399)) (literal (valuationOf q) (1403)) (countLit q [-21, -24]) (countLit q [-26, -29]) (count1402 q) 2 (meaning1399 q) (meaning1403 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause732 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1403 = true := counterClause732 (baseVal q)

theorem counterClause733 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1404 = true := by
  have hs : count1402 q = (countLit q [-21, -24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-26, -29])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1400)) (literal (valuationOf q) (1404)) (countLit q [-21, -24]) (countLit q [-26, -29]) (count1402 q) 2 1 (meaning1399 q) (meaning1400 q) (meaning1404 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1400 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause733 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1400 = false ∨ valuation q 1404 = true := counterClause733 (baseVal q)

theorem counterClause734 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1405 = true := by
  have hs : count1402 q = (countLit q [-21, -24]) + (countLit q [-26, -29]) := List.countP_append (p := literal q) (l₁ := [-21, -24]) (l₂ := [-26, -29])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1401)) (literal (valuationOf q) (1405)) (countLit q [-21, -24]) (countLit q [-26, -29]) (count1402 q) 2 2 (meaning1399 q) (meaning1401 q) (meaning1405 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1401 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause734 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1401 = false ∨ valuation q 1405 = true := counterClause734 (baseVal q)

theorem counterClause735 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1406 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_right (literal (valuationOf q) (1402)) (literal (valuationOf q) (1406)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 1 (meaning1402 q) (meaning1406 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause735 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1406 = true := counterClause735 (baseVal q)

theorem counterClause736 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1407 = true := by
  have hs : count1406 q = (countLit q [-15, -17, -18]) + (countLit q [-21, -24, -26, -29]) := List.countP_append (p := literal q) (l₁ := [-15, -17, -18]) (l₂ := [-21, -24, -26, -29])
  have hm := merge_right (literal (valuationOf q) (1403)) (literal (valuationOf q) (1407)) (countLit q [-15, -17, -18]) (countLit q [-21, -24, -26, -29]) (count1406 q) 2 (meaning1403 q) (meaning1407 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause736 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1407 = true := counterClause736 (baseVal q)

theorem block22 (q : Snake 81) (h : Conditions q) : B112E168.Block22 (valuation q) :=
  ⟨clause705 q h, clause706 q h, clause707 q h, clause708 q h, clause709 q h, clause710 q h, clause711 q h, clause712 q h, clause713 q h, clause714 q h, clause715 q h, clause716 q h, clause717 q h, clause718 q h, clause719 q h, clause720 q h, clause721 q h, clause722 q h, clause723 q h, clause724 q h, clause725 q h, clause726 q h, clause727 q h, clause728 q h, clause729 q h, clause730 q h, clause731 q h, clause732 q h, clause733 q h, clause734 q h, clause735 q h, clause736 q h⟩

end
end Snake9.Regrowth.E112168
