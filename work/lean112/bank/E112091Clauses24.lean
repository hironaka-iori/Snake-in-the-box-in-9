import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec24 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause769 (q : Nat → Bool) : valuationOf q 1386 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-70, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-75, -76])
  have hm := merge_right (literal (valuationOf q) (1386)) (literal (valuationOf q) (1388)) (countLit q [-70, -73]) (countLit q [-75, -76]) (count1388 q) 1 (meaning1386 q) (meaning1388 q) hs
  change valuationOf q 1386 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause769 (q : Snake 81) (h : Conditions q) : valuation q 1386 = false ∨ valuation q 1388 = true := counterClause769 (baseVal q)

theorem counterClause770 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1388 = true := by
  have hs : count1388 q = (countLit q [-70, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-75, -76])
  have hm := merge_left (literal (valuationOf q) (1384)) (literal (valuationOf q) (1388)) (countLit q [-70, -73]) (countLit q [-75, -76]) (count1388 q) 1 (meaning1384 q) (meaning1388 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1388 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause770 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1388 = true := counterClause770 (baseVal q)

theorem counterClause771 (q : Nat → Bool) : valuationOf q 1384 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true := by
  have hs : count1388 q = (countLit q [-70, -73]) + (countLit q [-75, -76]) := List.countP_append (p := literal q) (l₁ := [-70, -73]) (l₂ := [-75, -76])
  have hm := merge_two (literal (valuationOf q) (1384)) (literal (valuationOf q) (1386)) (literal (valuationOf q) (1389)) (countLit q [-70, -73]) (countLit q [-75, -76]) (count1388 q) 1 1 (meaning1384 q) (meaning1386 q) (meaning1389 q) hs
  change valuationOf q 1384 = false ∨ valuationOf q 1386 = false ∨ valuationOf q 1389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause771 (q : Snake 81) (h : Conditions q) : valuation q 1384 = false ∨ valuation q 1386 = false ∨ valuation q 1389 = true := counterClause771 (baseVal q)

theorem counterClause772 (q : Nat → Bool) : valuationOf q 1388 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -73, -75, -76])
  have hm := merge_right (literal (valuationOf q) (1388)) (literal (valuationOf q) (1392)) (countLit q [-63, -65, -68]) (countLit q [-70, -73, -75, -76]) (count1392 q) 1 (meaning1388 q) (meaning1392 q) hs
  change valuationOf q 1388 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause772 (q : Snake 81) (h : Conditions q) : valuation q 1388 = false ∨ valuation q 1392 = true := counterClause772 (baseVal q)

theorem counterClause773 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1392 = true := by
  have hs : count1392 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -73, -75, -76])
  have hm := merge_left (literal (valuationOf q) (1381)) (literal (valuationOf q) (1392)) (countLit q [-63, -65, -68]) (countLit q [-70, -73, -75, -76]) (count1392 q) 1 (meaning1381 q) (meaning1392 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1392 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause773 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1392 = true := counterClause773 (baseVal q)

theorem counterClause774 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1393)) (countLit q [-63, -65, -68]) (countLit q [-70, -73, -75, -76]) (count1392 q) 1 1 (meaning1381 q) (meaning1388 q) (meaning1393 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause774 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1388 = false ∨ valuation q 1393 = true := counterClause774 (baseVal q)

theorem counterClause775 (q : Nat → Bool) : valuationOf q 1381 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true := by
  have hs : count1392 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1381)) (literal (valuationOf q) (1389)) (literal (valuationOf q) (1394)) (countLit q [-63, -65, -68]) (countLit q [-70, -73, -75, -76]) (count1392 q) 1 2 (meaning1381 q) (meaning1389 q) (meaning1394 q) hs
  change valuationOf q 1381 = false ∨ valuationOf q 1389 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause775 (q : Snake 81) (h : Conditions q) : valuation q 1381 = false ∨ valuation q 1389 = false ∨ valuation q 1394 = true := counterClause775 (baseVal q)

theorem counterClause776 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1393 = true := by
  have hs : count1392 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -73, -75, -76])
  have hm := merge_left (literal (valuationOf q) (1382)) (literal (valuationOf q) (1393)) (countLit q [-63, -65, -68]) (countLit q [-70, -73, -75, -76]) (count1392 q) 2 (meaning1382 q) (meaning1393 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause776 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1393 = true := counterClause776 (baseVal q)

theorem counterClause777 (q : Nat → Bool) : valuationOf q 1382 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true := by
  have hs : count1392 q = (countLit q [-63, -65, -68]) + (countLit q [-70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-63, -65, -68]) (l₂ := [-70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1382)) (literal (valuationOf q) (1388)) (literal (valuationOf q) (1394)) (countLit q [-63, -65, -68]) (countLit q [-70, -73, -75, -76]) (count1392 q) 2 1 (meaning1382 q) (meaning1388 q) (meaning1394 q) hs
  change valuationOf q 1382 = false ∨ valuationOf q 1388 = false ∨ valuationOf q 1394 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause777 (q : Snake 81) (h : Conditions q) : valuation q 1382 = false ∨ valuation q 1388 = false ∨ valuation q 1394 = true := counterClause777 (baseVal q)

theorem counterClause778 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1399 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_left (literal (valuationOf q) (1373)) (literal (valuationOf q) (1399)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 1 (meaning1373 q) (meaning1399 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause778 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1399 = true := counterClause778 (baseVal q)

theorem counterClause779 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1400)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 1 1 (meaning1373 q) (meaning1392 q) (meaning1400 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause779 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1392 = false ∨ valuation q 1400 = true := counterClause779 (baseVal q)

theorem counterClause780 (q : Nat → Bool) : valuationOf q 1373 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1373)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1401)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 1 2 (meaning1373 q) (meaning1393 q) (meaning1401 q) hs
  change valuationOf q 1373 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause780 (q : Snake 81) (h : Conditions q) : valuation q 1373 = false ∨ valuation q 1393 = false ∨ valuation q 1401 = true := counterClause780 (baseVal q)

theorem counterClause781 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1400 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_left (literal (valuationOf q) (1374)) (literal (valuationOf q) (1400)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 2 (meaning1374 q) (meaning1400 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1400 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause781 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1400 = true := counterClause781 (baseVal q)

theorem counterClause782 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1401)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 2 1 (meaning1374 q) (meaning1392 q) (meaning1401 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause782 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1392 = false ∨ valuation q 1401 = true := counterClause782 (baseVal q)

theorem counterClause783 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1402)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 2 2 (meaning1374 q) (meaning1393 q) (meaning1402 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause783 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1393 = false ∨ valuation q 1402 = true := counterClause783 (baseVal q)

theorem counterClause784 (q : Nat → Bool) : valuationOf q 1374 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1374)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1403)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 2 3 (meaning1374 q) (meaning1394 q) (meaning1403 q) hs
  change valuationOf q 1374 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause784 (q : Snake 81) (h : Conditions q) : valuation q 1374 = false ∨ valuation q 1394 = false ∨ valuation q 1403 = true := counterClause784 (baseVal q)

theorem counterClause785 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1401 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_left (literal (valuationOf q) (1375)) (literal (valuationOf q) (1401)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 3 (meaning1375 q) (meaning1401 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause785 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1401 = true := counterClause785 (baseVal q)

theorem counterClause786 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1402)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 3 1 (meaning1375 q) (meaning1392 q) (meaning1402 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause786 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1392 = false ∨ valuation q 1402 = true := counterClause786 (baseVal q)

theorem counterClause787 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1403)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 3 2 (meaning1375 q) (meaning1393 q) (meaning1403 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause787 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1393 = false ∨ valuation q 1403 = true := counterClause787 (baseVal q)

theorem counterClause788 (q : Nat → Bool) : valuationOf q 1375 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1404 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1375)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1404)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 3 3 (meaning1375 q) (meaning1394 q) (meaning1404 q) hs
  change valuationOf q 1375 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause788 (q : Snake 81) (h : Conditions q) : valuation q 1375 = false ∨ valuation q 1394 = false ∨ valuation q 1404 = true := counterClause788 (baseVal q)

theorem counterClause789 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1402 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_left (literal (valuationOf q) (1376)) (literal (valuationOf q) (1402)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 4 (meaning1376 q) (meaning1402 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1402 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause789 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1402 = true := counterClause789 (baseVal q)

theorem counterClause790 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1403)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 4 1 (meaning1376 q) (meaning1392 q) (meaning1403 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause790 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1392 = false ∨ valuation q 1403 = true := counterClause790 (baseVal q)

theorem counterClause791 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1404 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1404)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 4 2 (meaning1376 q) (meaning1393 q) (meaning1404 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause791 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1393 = false ∨ valuation q 1404 = true := counterClause791 (baseVal q)

theorem counterClause792 (q : Nat → Bool) : valuationOf q 1376 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1405 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1376)) (literal (valuationOf q) (1394)) (literal (valuationOf q) (1405)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 4 3 (meaning1376 q) (meaning1394 q) (meaning1405 q) hs
  change valuationOf q 1376 = false ∨ valuationOf q 1394 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause792 (q : Snake 81) (h : Conditions q) : valuation q 1376 = false ∨ valuation q 1394 = false ∨ valuation q 1405 = true := counterClause792 (baseVal q)

theorem counterClause793 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1403 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_left (literal (valuationOf q) (1377)) (literal (valuationOf q) (1403)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 5 (meaning1377 q) (meaning1403 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause793 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1403 = true := counterClause793 (baseVal q)

theorem counterClause794 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1404 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1377)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1404)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 5 1 (meaning1377 q) (meaning1392 q) (meaning1404 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause794 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1392 = false ∨ valuation q 1404 = true := counterClause794 (baseVal q)

theorem counterClause795 (q : Nat → Bool) : valuationOf q 1377 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1405 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1377)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1405)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 5 2 (meaning1377 q) (meaning1393 q) (meaning1405 q) hs
  change valuationOf q 1377 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause795 (q : Snake 81) (h : Conditions q) : valuation q 1377 = false ∨ valuation q 1393 = false ∨ valuation q 1405 = true := counterClause795 (baseVal q)

theorem counterClause796 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1404 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_left (literal (valuationOf q) (1378)) (literal (valuationOf q) (1404)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 6 (meaning1378 q) (meaning1404 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1404 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause796 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1404 = true := counterClause796 (baseVal q)

theorem counterClause797 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1405 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1392)) (literal (valuationOf q) (1405)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 6 1 (meaning1378 q) (meaning1392 q) (meaning1405 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1392 = false ∨ valuationOf q 1405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause797 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1392 = false ∨ valuation q 1405 = true := counterClause797 (baseVal q)

theorem counterClause798 (q : Nat → Bool) : valuationOf q 1378 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1406 = true := by
  have hs : count1399 q = (countLit q [-52, -53, -55, -57, -61, -62]) + (countLit q [-63, -65, -68, -70, -73, -75, -76]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62]) (l₂ := [-63, -65, -68, -70, -73, -75, -76])
  have hm := merge_two (literal (valuationOf q) (1378)) (literal (valuationOf q) (1393)) (literal (valuationOf q) (1406)) (countLit q [-52, -53, -55, -57, -61, -62]) (countLit q [-63, -65, -68, -70, -73, -75, -76]) (count1399 q) 6 2 (meaning1378 q) (meaning1393 q) (meaning1406 q) hs
  change valuationOf q 1378 = false ∨ valuationOf q 1393 = false ∨ valuationOf q 1406 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause798 (q : Snake 81) (h : Conditions q) : valuation q 1378 = false ∨ valuation q 1393 = false ∨ valuation q 1406 = true := counterClause798 (baseVal q)

theorem counterClause799 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1412 = true := by
  have hs : count1412 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_right (literal (valuationOf q) (-83)) (literal (valuationOf q) (1412)) (countLit q [-81]) (countLit q [-83]) (count1412 q) 1 (meaningNeg83 q) (meaning1412 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause799 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1412 = true := counterClause799 (baseVal q)

theorem counterClause800 (q : Nat → Bool) : valuationOf q 81 = true ∨ valuationOf q 1412 = true := by
  have hs : count1412 q = (countLit q [-81]) + (countLit q [-83]) := List.countP_append (p := literal q) (l₁ := [-81]) (l₂ := [-83])
  have hm := merge_left (literal (valuationOf q) (-81)) (literal (valuationOf q) (1412)) (countLit q [-81]) (countLit q [-83]) (count1412 q) 1 (meaningNeg81 q) (meaning1412 q) hs
  change (! (valuationOf q 81)) = false ∨ valuationOf q 1412 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause800 (q : Snake 81) (h : Conditions q) : valuation q 81 = true ∨ valuation q 1412 = true := counterClause800 (baseVal q)

theorem block24 (q : Snake 81) (h : Conditions q) : B112E091.Block24 (valuation q) :=
  ⟨clause769 q h, clause770 q h, clause771 q h, clause772 q h, clause773 q h, clause774 q h, clause775 q h, clause776 q h, clause777 q h, clause778 q h, clause779 q h, clause780 q h, clause781 q h, clause782 q h, clause783 q h, clause784 q h, clause785 q h, clause786 q h, clause787 q h, clause788 q h, clause789 q h, clause790 q h, clause791 q h, clause792 q h, clause793 q h, clause794 q h, clause795 q h, clause796 q h, clause797 q h, clause798 q h, clause799 q h, clause800 q h⟩

end
end Snake9.Regrowth.E112091
