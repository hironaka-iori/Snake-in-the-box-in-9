import E112249Semantics
import B112E249Inputs
namespace Snake9.Regrowth.E112249
noncomputable section
local instance blockDec11 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause353 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1409 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1409)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 1 1 (meaning1386 q) (meaning1402 q) (meaning1409 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause353 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1402 = false ∨ valuation q 1409 = true := counterClause353 (baseVal q)

theorem counterClause354 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1410 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1410)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 1 2 (meaning1386 q) (meaning1403 q) (meaning1410 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause354 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1403 = false ∨ valuation q 1410 = true := counterClause354 (baseVal q)

theorem counterClause355 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1411 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1386)) (literal (valuationOf q) (1404)) (literal (valuationOf q) (1411)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 1 3 (meaning1386 q) (meaning1404 q) (meaning1411 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1404 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause355 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1404 = false ∨ valuation q 1411 = true := counterClause355 (baseVal q)

theorem counterClause356 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1409 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1387)) (literal (valuationOf q) (1409)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 2 (meaning1387 q) (meaning1409 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause356 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1409 = true := counterClause356 (baseVal q)

theorem counterClause357 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1410 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1410)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 2 1 (meaning1387 q) (meaning1402 q) (meaning1410 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause357 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1402 = false ∨ valuation q 1410 = true := counterClause357 (baseVal q)

theorem counterClause358 (q : Nat → Bool) : valuationOf q 1387 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1411 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1387)) (literal (valuationOf q) (1403)) (literal (valuationOf q) (1411)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 2 2 (meaning1387 q) (meaning1403 q) (meaning1411 q) hs
  change valuationOf q 1387 = false ∨ valuationOf q 1403 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause358 (q : Snake 81) (h : Conditions q) : valuation q 1387 = false ∨ valuation q 1403 = false ∨ valuation q 1411 = true := counterClause358 (baseVal q)

theorem counterClause359 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1410 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1388)) (literal (valuationOf q) (1410)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 3 (meaning1388 q) (meaning1410 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause359 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1410 = true := counterClause359 (baseVal q)

theorem counterClause360 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1411 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_two (literal (valuationOf q) (1388)) (literal (valuationOf q) (1402)) (literal (valuationOf q) (1411)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 3 1 (meaning1388 q) (meaning1402 q) (meaning1411 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1402 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause360 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1402 = false ∨ valuation q 1411 = true := counterClause360 (baseVal q)

theorem counterClause361 (q : Nat → Bool) : valuationOf q 1389 = false ∨ valuationOf q 1411 = true := by
  have hs : count1408 q = (countLit q [-54, -56, -59, -62, -64, -66]) + (countLit q [-67, -68, -72, -74, -78, -80]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -59, -62, -64, -66]) (l₂ := [-67, -68, -72, -74, -78, -80])
  have hm := merge_left (literal (valuationOf q) (1389)) (literal (valuationOf q) (1411)) (countLit q [-54, -56, -59, -62, -64, -66]) (countLit q [-67, -68, -72, -74, -78, -80]) (count1408 q) 4 (meaning1389 q) (meaning1411 q) hs
  change valuationOf q 1389 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause361 (q : Snake 81) (h : Conditions q) : valuation q 1389 = false ∨ valuation q 1411 = true := counterClause361 (baseVal q)

theorem counterClause362 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1417)) (countLit q [-82]) (countLit q [-84]) (count1417 q) 1 (meaningNeg84 q) (meaning1417 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause362 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1417 = true := counterClause362 (baseVal q)

theorem counterClause363 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-82]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-82]) (l₂ := [-84])
  have hm := merge_left (literal (valuationOf q) (-82)) (literal (valuationOf q) (1417)) (countLit q [-82]) (countLit q [-84]) (count1417 q) 1 (meaningNeg82 q) (meaning1417 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause363 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1417 = true := counterClause363 (baseVal q)

theorem counterClause364 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-81]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -84])
  have hm := merge_right (literal (valuationOf q) (1417)) (literal (valuationOf q) (1419)) (countLit q [-81]) (countLit q [-82, -84]) (count1419 q) 1 (meaning1417 q) (meaning1419 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause364 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1419 = true := counterClause364 (baseVal q)

theorem counterClause365 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-81]) + (countLit q [-82, -84]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-82, -84])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1419)) (countLit q [-81]) (countLit q [-82, -84]) (count1419 q) 1 (meaningNeg81 q) (meaning1419 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause365 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1419 = true := counterClause365 (baseVal q)

theorem counterClause366 (q : Nat → Bool) : valuationOf q 92 = true ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_right (literal (valuationOf q) (-92)) (literal (valuationOf q) (1422)) (countLit q [-89]) (countLit q [-92]) (count1422 q) 1 (meaningNeg92 q) (meaning1422 q) hs
  change (! (valuationOf q 92)) = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause366 (q : Snake 81) (h : Conditions q) : valuation q 92 = true ∨ valuation q 1422 = true := counterClause366 (baseVal q)

theorem counterClause367 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1422 = true := by
  have hs : count1422 q = (countLit q [-89]) + (countLit q [-92]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-92])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1422)) (countLit q [-89]) (countLit q [-92]) (count1422 q) 1 (meaningNeg89 q) (meaning1422 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause367 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1422 = true := counterClause367 (baseVal q)

theorem counterClause368 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1424 = true := by
  have hs : count1424 q = (countLit q [-86]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89, -92])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1424)) (countLit q [-86]) (countLit q [-89, -92]) (count1424 q) 1 (meaning1422 q) (meaning1424 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause368 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1424 = true := counterClause368 (baseVal q)

theorem counterClause369 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1424 = true := by
  have hs : count1424 q = (countLit q [-86]) + (countLit q [-89, -92]) := List.countP_append (p := literal q) (l₁ := [-86]) (l₂ := [-89, -92])
  have hm := merge_left (literal (valuationOf q) (-86)) (literal (valuationOf q) (1424)) (countLit q [-86]) (countLit q [-89, -92]) (count1424 q) 1 (meaningNeg86 q) (meaning1424 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1424 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause369 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1424 = true := counterClause369 (baseVal q)

theorem counterClause370 (q : Nat → Bool) : valuationOf q 1424 = false ∨ valuationOf q 1427 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-86, -89, -92]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-86, -89, -92])
  have hm := merge_right (literal (valuationOf q) (1424)) (literal (valuationOf q) (1427)) (countLit q [-81, -82, -84]) (countLit q [-86, -89, -92]) (count1427 q) 1 (meaning1424 q) (meaning1427 q) hs
  change valuationOf q 1424 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause370 (q : Snake 81) (h : Conditions q) : valuation q 1424 = false ∨ valuation q 1427 = true := counterClause370 (baseVal q)

theorem counterClause371 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1427 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-86, -89, -92]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-86, -89, -92])
  have hm := merge_left (literal (valuationOf q) (1419)) (literal (valuationOf q) (1427)) (countLit q [-81, -82, -84]) (countLit q [-86, -89, -92]) (count1427 q) 1 (meaning1419 q) (meaning1427 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause371 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1427 = true := counterClause371 (baseVal q)

theorem counterClause372 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1428 = true := by
  have hs : count1427 q = (countLit q [-81, -82, -84]) + (countLit q [-86, -89, -92]) := List.countP_append (p := literal q) (l₁ := [-81, -82, -84]) (l₂ := [-86, -89, -92])
  have hm := merge_two (literal (valuationOf q) (1419)) (literal (valuationOf q) (1424)) (literal (valuationOf q) (1428)) (countLit q [-81, -82, -84]) (countLit q [-86, -89, -92]) (count1427 q) 1 1 (meaning1419 q) (meaning1424 q) (meaning1428 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1424 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause372 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1424 = false ∨ valuation q 1428 = true := counterClause372 (baseVal q)

theorem counterClause373 (q : Nat → Bool) : valuationOf q 97 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_right (literal (valuationOf q) (-97)) (literal (valuationOf q) (1433)) (countLit q [-95]) (countLit q [-97]) (count1433 q) 1 (meaningNeg97 q) (meaning1433 q) hs
  change (! (valuationOf q 97)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause373 (q : Snake 81) (h : Conditions q) : valuation q 97 = true ∨ valuation q 1433 = true := counterClause373 (baseVal q)

theorem counterClause374 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 1433 = true := by
  have hs : count1433 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_left (literal (valuationOf q) (-95)) (literal (valuationOf q) (1433)) (countLit q [-95]) (countLit q [-97]) (count1433 q) 1 (meaningNeg95 q) (meaning1433 q) hs
  change (! (valuationOf q 95)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause374 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 1433 = true := counterClause374 (baseVal q)

theorem counterClause375 (q : Nat → Bool) : valuationOf q 95 = true ∨ valuationOf q 97 = true ∨ valuationOf q 1434 = true := by
  have hs : count1433 q = (countLit q [-95]) + (countLit q [-97]) := List.countP_append (p := literal q) (l₁ := [-95]) (l₂ := [-97])
  have hm := merge_two (literal (valuationOf q) (-95)) (literal (valuationOf q) (-97)) (literal (valuationOf q) (1434)) (countLit q [-95]) (countLit q [-97]) (count1433 q) 1 1 (meaningNeg95 q) (meaningNeg97 q) (meaning1434 q) hs
  change (! (valuationOf q 95)) = false ∨ (! (valuationOf q 97)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause375 (q : Snake 81) (h : Conditions q) : valuation q 95 = true ∨ valuation q 97 = true ∨ valuation q 1434 = true := counterClause375 (baseVal q)

theorem counterClause376 (q : Nat → Bool) : valuationOf q 1433 = false ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (1433)) (literal (valuationOf q) (1435)) (countLit q [-94]) (countLit q [-95, -97]) (count1435 q) 1 (meaning1433 q) (meaning1435 q) hs
  change valuationOf q 1433 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause376 (q : Snake 81) (h : Conditions q) : valuation q 1433 = false ∨ valuation q 1435 = true := counterClause376 (baseVal q)

theorem counterClause377 (q : Nat → Bool) : valuationOf q 1434 = false ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95, -97])
  have hm := merge_right (literal (valuationOf q) (1434)) (literal (valuationOf q) (1436)) (countLit q [-94]) (countLit q [-95, -97]) (count1435 q) 2 (meaning1434 q) (meaning1436 q) hs
  change valuationOf q 1434 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause377 (q : Snake 81) (h : Conditions q) : valuation q 1434 = false ∨ valuation q 1436 = true := counterClause377 (baseVal q)

theorem counterClause378 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1435 = true := by
  have hs : count1435 q = (countLit q [-94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95, -97])
  have hm := merge_left (literal (valuationOf q) (-94)) (literal (valuationOf q) (1435)) (countLit q [-94]) (countLit q [-95, -97]) (count1435 q) 1 (meaningNeg94 q) (meaning1435 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause378 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1435 = true := counterClause378 (baseVal q)

theorem counterClause379 (q : Nat → Bool) : valuationOf q 94 = true ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true := by
  have hs : count1435 q = (countLit q [-94]) + (countLit q [-95, -97]) := List.countP_append (p := literal q) (l₁ := [-94]) (l₂ := [-95, -97])
  have hm := merge_two (literal (valuationOf q) (-94)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1436)) (countLit q [-94]) (countLit q [-95, -97]) (count1435 q) 1 1 (meaningNeg94 q) (meaning1433 q) (meaning1436 q) hs
  change (! (valuationOf q 94)) = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause379 (q : Snake 81) (h : Conditions q) : valuation q 94 = true ∨ valuation q 1433 = false ∨ valuation q 1436 = true := counterClause379 (baseVal q)

theorem counterClause380 (q : Nat → Bool) : valuationOf q 102 = true ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_right (literal (valuationOf q) (-102)) (literal (valuationOf q) (1438)) (countLit q [-101]) (countLit q [-102]) (count1438 q) 1 (meaningNeg102 q) (meaning1438 q) hs
  change (! (valuationOf q 102)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause380 (q : Snake 81) (h : Conditions q) : valuation q 102 = true ∨ valuation q 1438 = true := counterClause380 (baseVal q)

theorem counterClause381 (q : Nat → Bool) : valuationOf q 101 = true ∨ valuationOf q 1438 = true := by
  have hs : count1438 q = (countLit q [-101]) + (countLit q [-102]) := List.countP_append (p := literal q) (l₁ := [-101]) (l₂ := [-102])
  have hm := merge_left (literal (valuationOf q) (-101)) (literal (valuationOf q) (1438)) (countLit q [-101]) (countLit q [-102]) (count1438 q) 1 (meaningNeg101 q) (meaning1438 q) hs
  change (! (valuationOf q 101)) = false ∨ valuationOf q 1438 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause381 (q : Snake 81) (h : Conditions q) : valuation q 101 = true ∨ valuation q 1438 = true := counterClause381 (baseVal q)

theorem counterClause382 (q : Nat → Bool) : valuationOf q 104 = true ∨ valuationOf q 1440 = true := by
  have hs : count1440 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_right (literal (valuationOf q) (-104)) (literal (valuationOf q) (1440)) (countLit q [-103]) (countLit q [-104]) (count1440 q) 1 (meaningNeg104 q) (meaning1440 q) hs
  change (! (valuationOf q 104)) = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause382 (q : Snake 81) (h : Conditions q) : valuation q 104 = true ∨ valuation q 1440 = true := counterClause382 (baseVal q)

theorem counterClause383 (q : Nat → Bool) : valuationOf q 103 = true ∨ valuationOf q 1440 = true := by
  have hs : count1440 q = (countLit q [-103]) + (countLit q [-104]) := List.countP_append (p := literal q) (l₁ := [-103]) (l₂ := [-104])
  have hm := merge_left (literal (valuationOf q) (-103)) (literal (valuationOf q) (1440)) (countLit q [-103]) (countLit q [-104]) (count1440 q) 1 (meaningNeg103 q) (meaning1440 q) hs
  change (! (valuationOf q 103)) = false ∨ valuationOf q 1440 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause383 (q : Snake 81) (h : Conditions q) : valuation q 103 = true ∨ valuation q 1440 = true := counterClause383 (baseVal q)

theorem counterClause384 (q : Nat → Bool) : valuationOf q 1440 = false ∨ valuationOf q 1442 = true := by
  have hs : count1442 q = (countLit q [-101, -102]) + (countLit q [-103, -104]) := List.countP_append (p := literal q) (l₁ := [-101, -102]) (l₂ := [-103, -104])
  have hm := merge_right (literal (valuationOf q) (1440)) (literal (valuationOf q) (1442)) (countLit q [-101, -102]) (countLit q [-103, -104]) (count1442 q) 1 (meaning1440 q) (meaning1442 q) hs
  change valuationOf q 1440 = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause384 (q : Snake 81) (h : Conditions q) : valuation q 1440 = false ∨ valuation q 1442 = true := counterClause384 (baseVal q)

theorem block11 (q : Snake 81) (h : Conditions q) : B112E249.Block11 (valuation q) :=
  ⟨clause353 q h, clause354 q h, clause355 q h, clause356 q h, clause357 q h, clause358 q h, clause359 q h, clause360 q h, clause361 q h, clause362 q h, clause363 q h, clause364 q h, clause365 q h, clause366 q h, clause367 q h, clause368 q h, clause369 q h, clause370 q h, clause371 q h, clause372 q h, clause373 q h, clause374 q h, clause375 q h, clause376 q h, clause377 q h, clause378 q h, clause379 q h, clause380 q h, clause381 q h, clause382 q h, clause383 q h, clause384 q h⟩

end
end Snake9.Regrowth.E112249
