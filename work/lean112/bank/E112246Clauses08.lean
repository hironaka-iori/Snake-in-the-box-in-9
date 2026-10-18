import E112246Semantics
import B112E246Inputs
namespace Snake9.Regrowth.E112246
noncomputable section
local instance blockDec8 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause257 (q : Nat → Bool) : valuationOf q 1379 = false ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -70])
  have hm := merge_right (literal (valuationOf q) (1379)) (literal (valuationOf q) (1381)) (countLit q [-65]) (countLit q [-67, -70]) (count1381 q) 1 (meaning1379 q) (meaning1381 q) hs
  change valuationOf q 1379 = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause257 (q : Snake 81) (h : Conditions q) : valuation q 1379 = false ∨ valuation q 1381 = true := counterClause257 (baseVal q)

theorem counterClause258 (q : Nat → Bool) : valuationOf q 1380 = false ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -70])
  have hm := merge_right (literal (valuationOf q) (1380)) (literal (valuationOf q) (1382)) (countLit q [-65]) (countLit q [-67, -70]) (count1381 q) 2 (meaning1380 q) (meaning1382 q) hs
  change valuationOf q 1380 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause258 (q : Snake 81) (h : Conditions q) : valuation q 1380 = false ∨ valuation q 1382 = true := counterClause258 (baseVal q)

theorem counterClause259 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -70])
  have hm := merge_left (literal (valuationOf q) (-65)) (literal (valuationOf q) (1381)) (countLit q [-65]) (countLit q [-67, -70]) (count1381 q) 1 (meaningNeg65 q) (meaning1381 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause259 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1381 = true := counterClause259 (baseVal q)

theorem counterClause260 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1379 = false ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -70])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1382)) (countLit q [-65]) (countLit q [-67, -70]) (count1381 q) 1 1 (meaningNeg65 q) (meaning1379 q) (meaning1382 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause260 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1379 = false ∨ valuation q 1382 = true := counterClause260 (baseVal q)

theorem counterClause261 (q : Nat → Bool) : valuationOf q 65 = true ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true := by
  have hs : count1381 q = (countLit q [-65]) + (countLit q [-67, -70]) := List.countP_append (p := literal q) (l₁ := [-65]) (l₂ := [-67, -70])
  have hm := merge_two (literal (valuationOf q) (-65)) (literal (valuationOf q) (1380)) (literal (valuationOf q) (1383)) (countLit q [-65]) (countLit q [-67, -70]) (count1381 q) 1 2 (meaningNeg65 q) (meaning1380 q) (meaning1383 q) hs
  change (! (valuationOf q 65)) = false ∨ valuationOf q 1380 = false ∨ valuationOf q 1383 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause261 (q : Snake 81) (h : Conditions q) : valuation q 65 = true ∨ valuation q 1380 = false ∨ valuation q 1383 = true := counterClause261 (baseVal q)

theorem counterClause262 (q : Nat → Bool) : valuationOf q 73 = true ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_right (literal (valuationOf q) (-73)) (literal (valuationOf q) (1384)) (countLit q [-71]) (countLit q [-73]) (count1384 q) 1 (meaningNeg73 q) (meaning1384 q) hs
  change (! (valuationOf q 73)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause262 (q : Snake 81) (h : Conditions q) : valuation q 73 = true ∨ valuation q 1384 = true := counterClause262 (baseVal q)

theorem counterClause263 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_left (literal (valuationOf q) (-71)) (literal (valuationOf q) (1384)) (countLit q [-71]) (countLit q [-73]) (count1384 q) 1 (meaningNeg71 q) (meaning1384 q) hs
  change (! (valuationOf q 71)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause263 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 1384 = true := counterClause263 (baseVal q)

theorem counterClause264 (q : Nat → Bool) : valuationOf q 71 = true ∨ valuationOf q 73 = true ∨ valuationOf q 1385 = true := by
  have hs : count1384 q = (countLit q [-71]) + (countLit q [-73]) := List.countP_append (p := literal q) (l₁ := [-71]) (l₂ := [-73])
  have hm := merge_two (literal (valuationOf q) (-71)) (literal (valuationOf q) (-73)) (literal (valuationOf q) (1385)) (countLit q [-71]) (countLit q [-73]) (count1384 q) 1 1 (meaningNeg71 q) (meaningNeg73 q) (meaning1385 q) hs
  change (! (valuationOf q 71)) = false ∨ (! (valuationOf q 73)) = false ∨ valuationOf q 1385 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause264 (q : Snake 81) (h : Conditions q) : valuation q 71 = true ∨ valuation q 73 = true ∨ valuation q 1385 = true := counterClause264 (baseVal q)

theorem counterClause265 (q : Nat → Bool) : valuationOf q 79 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_right (literal (valuationOf q) (-79)) (literal (valuationOf q) (1386)) (countLit q [-76]) (countLit q [-79]) (count1386 q) 1 (meaningNeg79 q) (meaning1386 q) hs
  change (! (valuationOf q 79)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause265 (q : Snake 81) (h : Conditions q) : valuation q 79 = true ∨ valuation q 1386 = true := counterClause265 (baseVal q)

theorem counterClause266 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_left (literal (valuationOf q) (-76)) (literal (valuationOf q) (1386)) (countLit q [-76]) (countLit q [-79]) (count1386 q) 1 (meaningNeg76 q) (meaning1386 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause266 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1386 = true := counterClause266 (baseVal q)

theorem counterClause267 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 79 = true ∨ valuationOf q 1387 = true := by
  have hs : count1386 q = (countLit q [-76]) + (countLit q [-79]) := List.countP_append (p := literal q) (l₁ := [-76]) (l₂ := [-79])
  have hm := merge_two (literal (valuationOf q) (-76)) (literal (valuationOf q) (-79)) (literal (valuationOf q) (1387)) (countLit q [-76]) (countLit q [-79]) (count1386 q) 1 1 (meaningNeg76 q) (meaningNeg79 q) (meaning1387 q) hs
  change (! (valuationOf q 76)) = false ∨ (! (valuationOf q 79)) = false ∨ valuationOf q 1387 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause267 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 79 = true ∨ valuation q 1387 = true := counterClause267 (baseVal q)

theorem counterClause268 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-71, -73]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-76, -79])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-71, -73]) (countLit q [-76, -79]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause268 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause268 (baseVal q)

theorem counterClause269 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-71, -73]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-76, -79])
  have hm := merge_right (literal (valuationOf q) (1387)) (literal (valuationOf q) (1389)) (countLit q [-71, -73]) (countLit q [-76, -79]) (count1388 q) 2 (meaning1387 q) (meaning1389 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause269 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1389 = true := counterClause269 (baseVal q)

theorem counterClause270 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-71, -73]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-76, -79])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (countLit q [-71, -73]) (countLit q [-76, -79]) (count1388 q) 1 (meaning1384 q) (meaning1388 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause270 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = true := counterClause270 (baseVal q)

theorem counterClause271 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-71, -73]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-76, -79])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1389)) (countLit q [-71, -73]) (countLit q [-76, -79]) (count1388 q) 1 1 (meaning1384 q) (meaning1386 q) (meaning1389 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause271 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1386 = false ∨ valuation q 1389 = true := counterClause271 (baseVal q)

theorem counterClause272 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1390 = true := by
  have hs : count1388 q = (countLit q [-71, -73]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-76, -79])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1390)) (countLit q [-71, -73]) (countLit q [-76, -79]) (count1388 q) 1 2 (meaning1384 q) (meaning1387 q) (meaning1390 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause272 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1387 = false ∨ valuation q 1390 = true := counterClause272 (baseVal q)

theorem counterClause273 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-71, -73]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-76, -79])
  have hm := merge_left (literal (valuationOf q) (1385)) (literal (valuationOf q) (1389)) (countLit q [-71, -73]) (countLit q [-76, -79]) (count1388 q) 2 (meaning1385 q) (meaning1389 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause273 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1389 = true := counterClause273 (baseVal q)

theorem counterClause274 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1390 = true := by
  have hs : count1388 q = (countLit q [-71, -73]) + (countLit q [-76, -79]) := List.countP_append (p := literal q) (l₁ := [-71, -73]) (l₂ := [-76, -79])
  have hm := merge_two (literal (valuationOf q) (1385)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1390)) (countLit q [-71, -73]) (countLit q [-76, -79]) (count1388 q) 2 1 (meaning1385 q) (meaning1386 q) (meaning1390 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1390 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause274 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1386 = false ∨ valuation q 1390 = true := counterClause274 (baseVal q)

theorem counterClause275 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-65, -67, -70]) + (countLit q [-71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -70]) (l₂ := [-71, -73, -76, -79])
  have hm := merge_right (literal (valuationOf q) (1388)) (literal (valuationOf q) (1392)) (countLit q [-65, -67, -70]) (countLit q [-71, -73, -76, -79]) (count1392 q) 1 (meaning1388 q) (meaning1392 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause275 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1392 = true := counterClause275 (baseVal q)

theorem counterClause276 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-65, -67, -70]) + (countLit q [-71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -70]) (l₂ := [-71, -73, -76, -79])
  have hm := merge_right (literal (valuationOf q) (1389)) (literal (valuationOf q) (1393)) (countLit q [-65, -67, -70]) (countLit q [-71, -73, -76, -79]) (count1392 q) 2 (meaning1389 q) (meaning1393 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause276 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1393 = true := counterClause276 (baseVal q)

theorem counterClause277 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-65, -67, -70]) + (countLit q [-71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -70]) (l₂ := [-71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1393)) (countLit q [-65, -67, -70]) (countLit q [-71, -73, -76, -79]) (count1392 q) 1 1 (meaning1381 q) (meaning1388 q) (meaning1393 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause277 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1388 = false ∨ valuation q 1393 = true := counterClause277 (baseVal q)

theorem counterClause278 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true := by
  have hs : count1392 q = (countLit q [-65, -67, -70]) + (countLit q [-71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -70]) (l₂ := [-71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1394)) (countLit q [-65, -67, -70]) (countLit q [-71, -73, -76, -79]) (count1392 q) 1 2 (meaning1381 q) (meaning1389 q) (meaning1394 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause278 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1389 = false ∨ valuation q 1394 = true := counterClause278 (baseVal q)

theorem counterClause279 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1395 = true := by
  have hs : count1392 q = (countLit q [-65, -67, -70]) + (countLit q [-71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -70]) (l₂ := [-71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1390)) (literal (valuationOf q) (1395)) (countLit q [-65, -67, -70]) (countLit q [-71, -73, -76, -79]) (count1392 q) 1 3 (meaning1381 q) (meaning1390 q) (meaning1395 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1390 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause279 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1390 = false ∨ valuation q 1395 = true := counterClause279 (baseVal q)

theorem counterClause280 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true := by
  have hs : count1392 q = (countLit q [-65, -67, -70]) + (countLit q [-71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -70]) (l₂ := [-71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1382)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1394)) (countLit q [-65, -67, -70]) (countLit q [-71, -73, -76, -79]) (count1392 q) 2 1 (meaning1382 q) (meaning1388 q) (meaning1394 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause280 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1388 = false ∨ valuation q 1394 = true := counterClause280 (baseVal q)

theorem counterClause281 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1395 = true := by
  have hs : count1392 q = (countLit q [-65, -67, -70]) + (countLit q [-71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -70]) (l₂ := [-71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1382)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1395)) (countLit q [-65, -67, -70]) (countLit q [-71, -73, -76, -79]) (count1392 q) 2 2 (meaning1382 q) (meaning1389 q) (meaning1395 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause281 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1389 = false ∨ valuation q 1395 = true := counterClause281 (baseVal q)

theorem counterClause282 (q : Nat → Bool) : valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1395 = true := by
  have hs : count1392 q = (countLit q [-65, -67, -70]) + (countLit q [-71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-65, -67, -70]) (l₂ := [-71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1383)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1395)) (countLit q [-65, -67, -70]) (countLit q [-71, -73, -76, -79]) (count1392 q) 3 1 (meaning1383 q) (meaning1388 q) (meaning1395 q) hs
  change valuationOf q 1383 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause282 (q : Snake 81) (h : Conditions q) : valuation q 1383 = false ∨ valuation q 1388 = false ∨ valuation q 1395 = true := counterClause282 (baseVal q)

theorem counterClause283 (q : Nat → Bool) : valuationOf q 1393 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_right (literal (valuationOf q) (1393)) (literal (valuationOf q) (1400)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 2 (meaning1393 q) (meaning1400 q) hs
  change valuationOf q 1393 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause283 (q : Snake 81) (h : Conditions q) : valuation q 1393 = false ∨ valuation q 1400 = true := counterClause283 (baseVal q)

theorem counterClause284 (q : Nat → Bool) : valuationOf q 1394 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_right (literal (valuationOf q) (1394)) (literal (valuationOf q) (1401)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 3 (meaning1394 q) (meaning1401 q) hs
  change valuationOf q 1394 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause284 (q : Snake 81) (h : Conditions q) : valuation q 1394 = false ∨ valuation q 1401 = true := counterClause284 (baseVal q)

theorem counterClause285 (q : Nat → Bool) : valuationOf q 1395 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_right (literal (valuationOf q) (1395)) (literal (valuationOf q) (1402)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 4 (meaning1395 q) (meaning1402 q) hs
  change valuationOf q 1395 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause285 (q : Snake 81) (h : Conditions q) : valuation q 1395 = false ∨ valuation q 1402 = true := counterClause285 (baseVal q)

theorem counterClause286 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1400)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 1 1 (meaning1373 q) (meaning1392 q) (meaning1400 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause286 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1392 = false ∨ valuation q 1400 = true := counterClause286 (baseVal q)

theorem counterClause287 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1401)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 1 2 (meaning1373 q) (meaning1393 q) (meaning1401 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause287 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1393 = false ∨ valuation q 1401 = true := counterClause287 (baseVal q)

theorem counterClause288 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-54, -55, -57, -60, -61, -64]) + (countLit q [-65, -67, -70, -71, -73, -76, -79]) := List.countP_append (p := literal q) (l₁ := [-54, -55, -57, -60, -61, -64]) (l₂ := [-65, -67, -70, -71, -73, -76, -79])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1402)) (countLit q [-54, -55, -57, -60, -61, -64]) (countLit q [-65, -67, -70, -71, -73, -76, -79]) (count1399 q) 1 3 (meaning1373 q) (meaning1394 q) (meaning1402 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause288 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1394 = false ∨ valuation q 1402 = true := counterClause288 (baseVal q)

theorem block8 (q : Snake 81) (h : Conditions q) : B112E246.Block8 (valuation q) :=
  ⟨clause257 q h, clause258 q h, clause259 q h, clause260 q h, clause261 q h, clause262 q h, clause263 q h, clause264 q h, clause265 q h, clause266 q h, clause267 q h, clause268 q h, clause269 q h, clause270 q h, clause271 q h, clause272 q h, clause273 q h, clause274 q h, clause275 q h, clause276 q h, clause277 q h, clause278 q h, clause279 q h, clause280 q h, clause281 q h, clause282 q h, clause283 q h, clause284 q h, clause285 q h, clause286 q h, clause287 q h, clause288 q h⟩

end
end Snake9.Regrowth.E112246
