import E112144Semantics
import B112E144Inputs
namespace Snake9.Regrowth.E112144
noncomputable section
local instance blockDec9 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause289 (q : Nat → Bool) : valuationOf q 66 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_right (literal (valuationOf q) (-66)) (literal (valuationOf q) (1368)) (countLit q [-63]) (countLit q [-66]) (count1368 q) 1 (meaningNeg66 q) (meaning1368 q) hs
  change (! (valuationOf q 66)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause289 (q : Snake 81) (h : Conditions q) : valuation q 66 = true ∨ valuation q 1368 = true := counterClause289 (baseVal q)

theorem counterClause290 (q : Nat → Bool) : valuationOf q 63 = true ∨ valuationOf q 1368 = true := by
  have hs : count1368 q = (countLit q [-63]) + (countLit q [-66]) := List.countP_append (p := literal q) (l₁ := [-63]) (l₂ := [-66])
  have hm := merge_left (literal (valuationOf q) (-63)) (literal (valuationOf q) (1368)) (countLit q [-63]) (countLit q [-66]) (count1368 q) 1 (meaningNeg63 q) (meaning1368 q) hs
  change (! (valuationOf q 63)) = false ∨ valuationOf q 1368 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause290 (q : Snake 81) (h : Conditions q) : valuation q 63 = true ∨ valuation q 1368 = true := counterClause290 (baseVal q)

theorem counterClause291 (q : Nat → Bool) : valuationOf q 1368 = false ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-60]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63, -66])
  have hm := merge_right (literal (valuationOf q) (1368)) (literal (valuationOf q) (1370)) (countLit q [-60]) (countLit q [-63, -66]) (count1370 q) 1 (meaning1368 q) (meaning1370 q) hs
  change valuationOf q 1368 = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause291 (q : Snake 81) (h : Conditions q) : valuation q 1368 = false ∨ valuation q 1370 = true := counterClause291 (baseVal q)

theorem counterClause292 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1370 = true := by
  have hs : count1370 q = (countLit q [-60]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63, -66])
  have hm := merge_left (literal (valuationOf q) (-60)) (literal (valuationOf q) (1370)) (countLit q [-60]) (countLit q [-63, -66]) (count1370 q) 1 (meaningNeg60 q) (meaning1370 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1370 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause292 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1370 = true := counterClause292 (baseVal q)

theorem counterClause293 (q : Nat → Bool) : valuationOf q 60 = true ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true := by
  have hs : count1370 q = (countLit q [-60]) + (countLit q [-63, -66]) := List.countP_append (p := literal q) (l₁ := [-60]) (l₂ := [-63, -66])
  have hm := merge_two (literal (valuationOf q) (-60)) (literal (valuationOf q) (1368)) (literal (valuationOf q) (1371)) (countLit q [-60]) (countLit q [-63, -66]) (count1370 q) 1 1 (meaningNeg60 q) (meaning1368 q) (meaning1371 q) hs
  change (! (valuationOf q 60)) = false ∨ valuationOf q 1368 = false ∨ valuationOf q 1371 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause293 (q : Snake 81) (h : Conditions q) : valuation q 60 = true ∨ valuation q 1368 = false ∨ valuation q 1371 = true := counterClause293 (baseVal q)

theorem counterClause294 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1373 = true := by
  have hs : count1373 q = (countLit q [-54, -56, -58]) + (countLit q [-60, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58]) (l₂ := [-60, -63, -66])
  have hm := merge_left (literal (valuationOf q) (1365)) (literal (valuationOf q) (1373)) (countLit q [-54, -56, -58]) (countLit q [-60, -63, -66]) (count1373 q) 1 (meaning1365 q) (meaning1373 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause294 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1373 = true := counterClause294 (baseVal q)

theorem counterClause295 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-54, -56, -58]) + (countLit q [-60, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58]) (l₂ := [-60, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1374)) (countLit q [-54, -56, -58]) (countLit q [-60, -63, -66]) (count1373 q) 1 1 (meaning1365 q) (meaning1370 q) (meaning1374 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause295 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1370 = false ∨ valuation q 1374 = true := counterClause295 (baseVal q)

theorem counterClause296 (q : Nat → Bool) : valuationOf q 1365 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-54, -56, -58]) + (countLit q [-60, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58]) (l₂ := [-60, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1365)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1375)) (countLit q [-54, -56, -58]) (countLit q [-60, -63, -66]) (count1373 q) 1 2 (meaning1365 q) (meaning1371 q) (meaning1375 q) hs
  change valuationOf q 1365 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause296 (q : Snake 81) (h : Conditions q) : valuation q 1365 = false ∨ valuation q 1371 = false ∨ valuation q 1375 = true := counterClause296 (baseVal q)

theorem counterClause297 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1374 = true := by
  have hs : count1373 q = (countLit q [-54, -56, -58]) + (countLit q [-60, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58]) (l₂ := [-60, -63, -66])
  have hm := merge_left (literal (valuationOf q) (1366)) (literal (valuationOf q) (1374)) (countLit q [-54, -56, -58]) (countLit q [-60, -63, -66]) (count1373 q) 2 (meaning1366 q) (meaning1374 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1374 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause297 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1374 = true := counterClause297 (baseVal q)

theorem counterClause298 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true := by
  have hs : count1373 q = (countLit q [-54, -56, -58]) + (countLit q [-60, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58]) (l₂ := [-60, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1370)) (literal (valuationOf q) (1375)) (countLit q [-54, -56, -58]) (countLit q [-60, -63, -66]) (count1373 q) 2 1 (meaning1366 q) (meaning1370 q) (meaning1375 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1370 = false ∨ valuationOf q 1375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause298 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1370 = false ∨ valuation q 1375 = true := counterClause298 (baseVal q)

theorem counterClause299 (q : Nat → Bool) : valuationOf q 1366 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1376 = true := by
  have hs : count1373 q = (countLit q [-54, -56, -58]) + (countLit q [-60, -63, -66]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58]) (l₂ := [-60, -63, -66])
  have hm := merge_two (literal (valuationOf q) (1366)) (literal (valuationOf q) (1371)) (literal (valuationOf q) (1376)) (countLit q [-54, -56, -58]) (countLit q [-60, -63, -66]) (count1373 q) 2 2 (meaning1366 q) (meaning1371 q) (meaning1376 q) hs
  change valuationOf q 1366 = false ∨ valuationOf q 1371 = false ∨ valuationOf q 1376 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause299 (q : Snake 81) (h : Conditions q) : valuation q 1366 = false ∨ valuation q 1371 = false ∨ valuation q 1376 = true := counterClause299 (baseVal q)

theorem counterClause300 (q : Nat → Bool) : valuationOf q 70 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_right (literal (valuationOf q) (-70)) (literal (valuationOf q) (1379)) (countLit q [-69]) (countLit q [-70]) (count1379 q) 1 (meaningNeg70 q) (meaning1379 q) hs
  change (! (valuationOf q 70)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause300 (q : Snake 81) (h : Conditions q) : valuation q 70 = true ∨ valuation q 1379 = true := counterClause300 (baseVal q)

theorem counterClause301 (q : Nat → Bool) : valuationOf q 69 = true ∨ valuationOf q 1379 = true := by
  have hs : count1379 q = (countLit q [-69]) + (countLit q [-70]) := List.countP_append (p := literal q) (l₁ := [-69]) (l₂ := [-70])
  have hm := merge_left (literal (valuationOf q) (-69)) (literal (valuationOf q) (1379)) (countLit q [-69]) (countLit q [-70]) (count1379 q) 1 (meaningNeg69 q) (meaning1379 q) hs
  change (! (valuationOf q 69)) = false ∨ valuationOf q 1379 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause301 (q : Snake 81) (h : Conditions q) : valuation q 69 = true ∨ valuation q 1379 = true := counterClause301 (baseVal q)

theorem counterClause302 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1381 = true := by
  have hs : count1381 q = (countLit q [-67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (-67)) (literal (valuationOf q) (1381)) (countLit q [-67]) (countLit q [-69, -70]) (count1381 q) 1 (meaningNeg67 q) (meaning1381 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1381 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause302 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1381 = true := counterClause302 (baseVal q)

theorem counterClause303 (q : Nat → Bool) : valuationOf q 67 = true ∨ valuationOf q 1379 = false ∨ valuationOf q 1382 = true := by
  have hs : count1381 q = (countLit q [-67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-67]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (-67)) (literal (valuationOf q) (1379)) (literal (valuationOf q) (1382)) (countLit q [-67]) (countLit q [-69, -70]) (count1381 q) 1 1 (meaningNeg67 q) (meaning1379 q) (meaning1382 q) hs
  change (! (valuationOf q 67)) = false ∨ valuationOf q 1379 = false ∨ valuationOf q 1382 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause303 (q : Snake 81) (h : Conditions q) : valuation q 67 = true ∨ valuation q 1379 = false ∨ valuation q 1382 = true := counterClause303 (baseVal q)

theorem counterClause304 (q : Nat → Bool) : valuationOf q 76 = true ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_right (literal (valuationOf q) (-76)) (literal (valuationOf q) (1384)) (countLit q [-74]) (countLit q [-76]) (count1384 q) 1 (meaningNeg76 q) (meaning1384 q) hs
  change (! (valuationOf q 76)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause304 (q : Snake 81) (h : Conditions q) : valuation q 76 = true ∨ valuation q 1384 = true := counterClause304 (baseVal q)

theorem counterClause305 (q : Nat → Bool) : valuationOf q 74 = true ∨ valuationOf q 1384 = true := by
  have hs : count1384 q = (countLit q [-74]) + (countLit q [-76]) := List.countP_append (p := literal q) (l₁ := [-74]) (l₂ := [-76])
  have hm := merge_left (literal (valuationOf q) (-74)) (literal (valuationOf q) (1384)) (countLit q [-74]) (countLit q [-76]) (count1384 q) 1 (meaningNeg74 q) (meaning1384 q) hs
  change (! (valuationOf q 74)) = false ∨ valuationOf q 1384 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause305 (q : Snake 81) (h : Conditions q) : valuation q 74 = true ∨ valuation q 1384 = true := counterClause305 (baseVal q)

theorem counterClause306 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_right (literal (valuationOf q) (-78)) (literal (valuationOf q) (1386)) (countLit q [-77]) (countLit q [-78]) (count1386 q) 1 (meaningNeg78 q) (meaning1386 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause306 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1386 = true := counterClause306 (baseVal q)

theorem counterClause307 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1386 = true := by
  have hs : count1386 q = (countLit q [-77]) + (countLit q [-78]) := List.countP_append (p := literal q) (l₁ := [-77]) (l₂ := [-78])
  have hm := merge_left (literal (valuationOf q) (-77)) (literal (valuationOf q) (1386)) (countLit q [-77]) (countLit q [-78]) (count1386 q) 1 (meaningNeg77 q) (meaning1386 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1386 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause307 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1386 = true := counterClause307 (baseVal q)

theorem counterClause308 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-74, -76]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -78])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-74, -76]) (countLit q [-77, -78]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause308 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause308 (baseVal q)

theorem counterClause309 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-74, -76]) + (countLit q [-77, -78]) := List.countP_append (p := literal q) (l₁ := [-74, -76]) (l₂ := [-77, -78])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (countLit q [-74, -76]) (countLit q [-77, -78]) (count1388 q) 1 (meaning1384 q) (meaning1388 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause309 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = true := counterClause309 (baseVal q)

theorem counterClause310 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-67, -69, -70]) + (countLit q [-74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -70]) (l₂ := [-74, -76, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1393)) (countLit q [-67, -69, -70]) (countLit q [-74, -76, -77, -78]) (count1392 q) 1 1 (meaning1381 q) (meaning1388 q) (meaning1393 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause310 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1388 = false ∨ valuation q 1393 = true := counterClause310 (baseVal q)

theorem counterClause311 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-67, -69, -70]) + (countLit q [-74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -70]) (l₂ := [-74, -76, -77, -78])
  have hm := merge_left (literal (valuationOf q) (1382)) (literal (valuationOf q) (1393)) (countLit q [-67, -69, -70]) (countLit q [-74, -76, -77, -78]) (count1392 q) 2 (meaning1382 q) (meaning1393 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause311 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1393 = true := counterClause311 (baseVal q)

theorem counterClause312 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true := by
  have hs : count1392 q = (countLit q [-67, -69, -70]) + (countLit q [-74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-67, -69, -70]) (l₂ := [-74, -76, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1382)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1394)) (countLit q [-67, -69, -70]) (countLit q [-74, -76, -77, -78]) (count1392 q) 2 1 (meaning1382 q) (meaning1388 q) (meaning1394 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause312 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1388 = false ∨ valuation q 1394 = true := counterClause312 (baseVal q)

theorem counterClause313 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-54, -56, -58, -60, -63, -66]) + (countLit q [-67, -69, -70, -74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66]) (l₂ := [-67, -69, -70, -74, -76, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1401)) (countLit q [-54, -56, -58, -60, -63, -66]) (countLit q [-67, -69, -70, -74, -76, -77, -78]) (count1399 q) 1 2 (meaning1373 q) (meaning1393 q) (meaning1401 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause313 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1393 = false ∨ valuation q 1401 = true := counterClause313 (baseVal q)

theorem counterClause314 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-54, -56, -58, -60, -63, -66]) + (countLit q [-67, -69, -70, -74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66]) (l₂ := [-67, -69, -70, -74, -76, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1402)) (countLit q [-54, -56, -58, -60, -63, -66]) (countLit q [-67, -69, -70, -74, -76, -77, -78]) (count1399 q) 1 3 (meaning1373 q) (meaning1394 q) (meaning1402 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause314 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1394 = false ∨ valuation q 1402 = true := counterClause314 (baseVal q)

theorem counterClause315 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-54, -56, -58, -60, -63, -66]) + (countLit q [-67, -69, -70, -74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66]) (l₂ := [-67, -69, -70, -74, -76, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1402)) (countLit q [-54, -56, -58, -60, -63, -66]) (countLit q [-67, -69, -70, -74, -76, -77, -78]) (count1399 q) 2 2 (meaning1374 q) (meaning1393 q) (meaning1402 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause315 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1393 = false ∨ valuation q 1402 = true := counterClause315 (baseVal q)

theorem counterClause316 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-54, -56, -58, -60, -63, -66]) + (countLit q [-67, -69, -70, -74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66]) (l₂ := [-67, -69, -70, -74, -76, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1403)) (countLit q [-54, -56, -58, -60, -63, -66]) (countLit q [-67, -69, -70, -74, -76, -77, -78]) (count1399 q) 2 3 (meaning1374 q) (meaning1394 q) (meaning1403 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause316 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1394 = false ∨ valuation q 1403 = true := counterClause316 (baseVal q)

theorem counterClause317 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-54, -56, -58, -60, -63, -66]) + (countLit q [-67, -69, -70, -74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66]) (l₂ := [-67, -69, -70, -74, -76, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1403)) (countLit q [-54, -56, -58, -60, -63, -66]) (countLit q [-67, -69, -70, -74, -76, -77, -78]) (count1399 q) 3 2 (meaning1375 q) (meaning1393 q) (meaning1403 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause317 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1393 = false ∨ valuation q 1403 = true := counterClause317 (baseVal q)

theorem counterClause318 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1404 = true := by
  have hs : count1399 q = (countLit q [-54, -56, -58, -60, -63, -66]) + (countLit q [-67, -69, -70, -74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66]) (l₂ := [-67, -69, -70, -74, -76, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1404)) (countLit q [-54, -56, -58, -60, -63, -66]) (countLit q [-67, -69, -70, -74, -76, -77, -78]) (count1399 q) 3 3 (meaning1375 q) (meaning1394 q) (meaning1404 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause318 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1394 = false ∨ valuation q 1404 = true := counterClause318 (baseVal q)

theorem counterClause319 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1404 = true := by
  have hs : count1399 q = (countLit q [-54, -56, -58, -60, -63, -66]) + (countLit q [-67, -69, -70, -74, -76, -77, -78]) := List.countP_append (p := literal q) (l₁ := [-54, -56, -58, -60, -63, -66]) (l₂ := [-67, -69, -70, -74, -76, -77, -78])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1404)) (countLit q [-54, -56, -58, -60, -63, -66]) (countLit q [-67, -69, -70, -74, -76, -77, -78]) (count1399 q) 4 2 (meaning1376 q) (meaning1393 q) (meaning1404 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause319 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1393 = false ∨ valuation q 1404 = true := counterClause319 (baseVal q)

theorem counterClause320 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1412 = true := by
  have hs : count1412 q = (countLit q [-83]) + (countLit q [-84]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-84])
  have hm := merge_right (literal (valuationOf q) (-84)) (literal (valuationOf q) (1412)) (countLit q [-83]) (countLit q [-84]) (count1412 q) 1 (meaningNeg84 q) (meaning1412 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause320 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1412 = true := counterClause320 (baseVal q)

theorem block9 (q : Snake 81) (h : Conditions q) : B112E144.Block9 (valuation q) :=
  ⟨clause289 q h, clause290 q h, clause291 q h, clause292 q h, clause293 q h, clause294 q h, clause295 q h, clause296 q h, clause297 q h, clause298 q h, clause299 q h, clause300 q h, clause301 q h, clause302 q h, clause303 q h, clause304 q h, clause305 q h, clause306 q h, clause307 q h, clause308 q h, clause309 q h, clause310 q h, clause311 q h, clause312 q h, clause313 q h, clause314 q h, clause315 q h, clause316 q h, clause317 q h, clause318 q h, clause319 q h, clause320 q h⟩

end
end Snake9.Regrowth.E112144
