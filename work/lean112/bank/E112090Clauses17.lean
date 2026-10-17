import E112090Semantics
import B112E090Inputs
namespace Snake9.Regrowth.E112090
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1398 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1384)) (literal (valuationOf q) (1398)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 5 (meaning1384 q) (meaning1398 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1398 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 1385 = false ∨ valuationOf q 1399 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_right (literal (valuationOf q) (1385)) (literal (valuationOf q) (1399)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 6 (meaning1385 q) (meaning1399 q) hs
  change valuationOf q 1385 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 1385 = false ∨ valuation q 1399 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1400 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1400)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 1 6 (meaning1327 q) (meaning1385 q) (meaning1400 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1385 = false ∨ valuation q 1400 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 1327 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1327)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1401)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 1 7 (meaning1327 q) (meaning1386 q) (meaning1401 q) hs
  change valuationOf q 1327 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 1327 = false ∨ valuation q 1386 = false ∨ valuation q 1401 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1398 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1398)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 2 3 (meaning1328 q) (meaning1382 q) (meaning1398 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1398 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1382 = false ∨ valuation q 1398 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1399 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1399)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 2 4 (meaning1328 q) (meaning1383 q) (meaning1399 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1383 = false ∨ valuation q 1399 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1400 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1400)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 2 5 (meaning1328 q) (meaning1384 q) (meaning1400 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1384 = false ∨ valuation q 1400 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1401)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 2 6 (meaning1328 q) (meaning1385 q) (meaning1401 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1385 = false ∨ valuation q 1401 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1402 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1402)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 2 7 (meaning1328 q) (meaning1386 q) (meaning1402 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1386 = false ∨ valuation q 1402 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 1328 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1403 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1328)) (literal (valuationOf q) (1387)) (literal (valuationOf q) (1403)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 2 8 (meaning1328 q) (meaning1387 q) (meaning1403 q) hs
  change valuationOf q 1328 = false ∨ valuationOf q 1387 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 1328 = false ∨ valuation q 1387 = false ∨ valuation q 1403 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1399 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1399)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 3 3 (meaning1329 q) (meaning1382 q) (meaning1399 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1382 = false ∨ valuation q 1399 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1400 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1400)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 3 4 (meaning1329 q) (meaning1383 q) (meaning1400 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1383 = false ∨ valuation q 1400 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1401)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 3 5 (meaning1329 q) (meaning1384 q) (meaning1401 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1384 = false ∨ valuation q 1401 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1402 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1402)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 3 6 (meaning1329 q) (meaning1385 q) (meaning1402 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1385 = false ∨ valuation q 1402 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 1329 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1403 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1329)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1403)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 3 7 (meaning1329 q) (meaning1386 q) (meaning1403 q) hs
  change valuationOf q 1329 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 1329 = false ∨ valuation q 1386 = false ∨ valuation q 1403 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1400 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1382)) (literal (valuationOf q) (1400)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 4 3 (meaning1330 q) (meaning1382 q) (meaning1400 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1382 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1382 = false ∨ valuation q 1400 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1401 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1383)) (literal (valuationOf q) (1401)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 4 4 (meaning1330 q) (meaning1383 q) (meaning1401 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1383 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1383 = false ∨ valuation q 1401 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1402 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1384)) (literal (valuationOf q) (1402)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 4 5 (meaning1330 q) (meaning1384 q) (meaning1402 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1384 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1384 = false ∨ valuation q 1402 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 1330 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1403 = true := by
  have hs : count1394 q = (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) + (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (l₂ := [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52])
  have hm := merge_two (literal (valuationOf q) (1330)) (literal (valuationOf q) (1385)) (literal (valuationOf q) (1403)) (countLit q [-3, -4, -5, -8, -9, -13, -14, -16, -18, -20, -22, -23, -24]) (countLit q [-27, -29, -31, -33, -35, -36, -39, -40, -42, -45, -46, -48, -50, -52]) (count1394 q) 4 6 (meaning1330 q) (meaning1385 q) (meaning1403 q) hs
  change valuationOf q 1330 = false ∨ valuationOf q 1385 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 1330 = false ∨ valuation q 1385 = false ∨ valuation q 1403 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 1409 = true := by
  have hs : count1409 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_left (literal (valuationOf q) (-55)) (literal (valuationOf q) (1409)) (countLit q [-55]) (countLit q [-56]) (count1409 q) 1 (meaningNeg55 q) (meaning1409 q) hs
  change (! (valuationOf q 55)) = false ∨ valuationOf q 1409 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 1409 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 55 = true ∨ valuationOf q 56 = true ∨ valuationOf q 1410 = true := by
  have hs : count1409 q = (countLit q [-55]) + (countLit q [-56]) := List.countP_append (p := literal q) (l₁ := [-55]) (l₂ := [-56])
  have hm := merge_two (literal (valuationOf q) (-55)) (literal (valuationOf q) (-56)) (literal (valuationOf q) (1410)) (countLit q [-55]) (countLit q [-56]) (count1409 q) 1 1 (meaningNeg55 q) (meaningNeg56 q) (meaning1410 q) hs
  change (! (valuationOf q 55)) = false ∨ (! (valuationOf q 56)) = false ∨ valuationOf q 1410 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 55 = true ∨ valuation q 56 = true ∨ valuation q 1410 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 1409 = false ∨ valuationOf q 1411 = true := by
  have hs : count1411 q = (countLit q [-54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -56])
  have hm := merge_right (literal (valuationOf q) (1409)) (literal (valuationOf q) (1411)) (countLit q [-54]) (countLit q [-55, -56]) (count1411 q) 1 (meaning1409 q) (meaning1411 q) hs
  change valuationOf q 1409 = false ∨ valuationOf q 1411 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 1409 = false ∨ valuation q 1411 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 1410 = false ∨ valuationOf q 1412 = true := by
  have hs : count1411 q = (countLit q [-54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -56])
  have hm := merge_right (literal (valuationOf q) (1410)) (literal (valuationOf q) (1412)) (countLit q [-54]) (countLit q [-55, -56]) (count1411 q) 2 (meaning1410 q) (meaning1412 q) hs
  change valuationOf q 1410 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 1410 = false ∨ valuation q 1412 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1409 = false ∨ valuationOf q 1412 = true := by
  have hs : count1411 q = (countLit q [-54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (1409)) (literal (valuationOf q) (1412)) (countLit q [-54]) (countLit q [-55, -56]) (count1411 q) 1 1 (meaningNeg54 q) (meaning1409 q) (meaning1412 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1409 = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1409 = false ∨ valuation q 1412 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 54 = true ∨ valuationOf q 1410 = false ∨ valuationOf q 1413 = true := by
  have hs : count1411 q = (countLit q [-54]) + (countLit q [-55, -56]) := List.countP_append (p := literal q) (l₁ := [-54]) (l₂ := [-55, -56])
  have hm := merge_two (literal (valuationOf q) (-54)) (literal (valuationOf q) (1410)) (literal (valuationOf q) (1413)) (countLit q [-54]) (countLit q [-55, -56]) (count1411 q) 1 2 (meaningNeg54 q) (meaning1410 q) (meaning1413 q) hs
  change (! (valuationOf q 54)) = false ∨ valuationOf q 1410 = false ∨ valuationOf q 1413 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 54 = true ∨ valuation q 1410 = false ∨ valuation q 1413 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 61 = true ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_right (literal (valuationOf q) (-61)) (literal (valuationOf q) (1414)) (countLit q [-58]) (countLit q [-61]) (count1414 q) 1 (meaningNeg61 q) (meaning1414 q) hs
  change (! (valuationOf q 61)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 61 = true ∨ valuation q 1414 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_left (literal (valuationOf q) (-58)) (literal (valuationOf q) (1414)) (countLit q [-58]) (countLit q [-61]) (count1414 q) 1 (meaningNeg58 q) (meaning1414 q) hs
  change (! (valuationOf q 58)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 1414 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 58 = true ∨ valuationOf q 61 = true ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-58]) + (countLit q [-61]) := List.countP_append (p := literal q) (l₁ := [-58]) (l₂ := [-61])
  have hm := merge_two (literal (valuationOf q) (-58)) (literal (valuationOf q) (-61)) (literal (valuationOf q) (1415)) (countLit q [-58]) (countLit q [-61]) (count1414 q) 1 1 (meaningNeg58 q) (meaningNeg61 q) (meaning1415 q) hs
  change (! (valuationOf q 58)) = false ∨ (! (valuationOf q 61)) = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 58 = true ∨ valuation q 61 = true ∨ valuation q 1415 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1416)) (countLit q [-63]) (countLit q [-66]) (count1416 q) 1 (meaningNeg66 q) (meaning1416 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1416 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1416 = true := by
  have hs : count1416 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1416)) (countLit q [-63]) (countLit q [-66]) (count1416 q) 1 (meaningNeg63 q) (meaning1416 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1416 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1416 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 66 = true ∨ valuationOf q 1417 = true := by
  have hs : count1416 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_two (literal (valuationOf q) (-63)) (literal (valuationOf q) (-66)) (literal (valuationOf q) (1417)) (countLit q [-63]) (countLit q [-66]) (count1416 q) 1 1 (meaningNeg63 q) (meaningNeg66 q) (meaning1417 q) hs
  change (! (valuationOf q 63)) = false ∨ (! (valuationOf q 66)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 66 = true ∨ valuation q 1417 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 1416 = false ∨ valuationOf q 1418 = true := by
  have hs : count1418 q = (countLit q [-58, -61]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-58, -61]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1416)) (literal (valuationOf q) (1418)) (countLit q [-58, -61]) (countLit q [-63, -66]) (count1418 q) 1 (meaning1416 q) (meaning1418 q) hs
  change valuationOf q 1416 = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 1416 = false ∨ valuation q 1418 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E090.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112090
