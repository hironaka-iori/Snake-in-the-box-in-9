import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec27 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause865 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1454 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1427)) (literal (valuationOf q) (1454)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 3 (meaning1427 q) (meaning1454 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause865 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1454 = true := counterClause865 (baseVal q)

theorem counterClause866 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1445)) (literal (valuationOf q) (1455)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 3 1 (meaning1427 q) (meaning1445 q) (meaning1455 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1445 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause866 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1445 = false ∨ valuation q 1455 = true := counterClause866 (baseVal q)

theorem counterClause867 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1456 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1456)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 3 2 (meaning1427 q) (meaning1446 q) (meaning1456 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause867 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1446 = false ∨ valuation q 1456 = true := counterClause867 (baseVal q)

theorem counterClause868 (q : Nat → Bool) : valuationOf q 1427 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1457 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1427)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1457)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 3 3 (meaning1427 q) (meaning1447 q) (meaning1457 q) hs
  change valuationOf q 1427 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause868 (q : Snake 81) (h : Conditions q) : valuation q 1427 = false ∨ valuation q 1447 = false ∨ valuation q 1457 = true := counterClause868 (baseVal q)

theorem counterClause869 (q : Nat → Bool) : valuationOf q 1428 = false ∨ valuationOf q 1455 = true := by
  have hs : count1452 q = (countLit q [-78, -81, -83, -85, -87, -89, -91]) + (countLit q [-93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83, -85, -87, -89, -91]) (l₂ := [-93, -96, -98, -100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1428)) (literal (valuationOf q) (1455)) (countLit q [-78, -81, -83, -85, -87, -89, -91]) (countLit q [-93, -96, -98, -100, -102, -103, -105]) (count1452 q) 4 (meaning1428 q) (meaning1455 q) hs
  change valuationOf q 1428 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause869 (q : Snake 81) (h : Conditions q) : valuation q 1428 = false ∨ valuation q 1455 = true := counterClause869 (baseVal q)

theorem counterClause870 (q : Nat → Bool) : valuationOf q 1399 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1399)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1471)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 1 6 (meaning1399 q) (meaning1457 q) (meaning1471 q) hs
  change valuationOf q 1399 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause870 (q : Snake 81) (h : Conditions q) : valuation q 1399 = false ∨ valuation q 1457 = false ∨ valuation q 1471 = true := counterClause870 (baseVal q)

theorem counterClause871 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1468 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1468)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 2 2 (meaning1400 q) (meaning1453 q) (meaning1468 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause871 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1453 = false ∨ valuation q 1468 = true := counterClause871 (baseVal q)

theorem counterClause872 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1469 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1469)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 2 3 (meaning1400 q) (meaning1454 q) (meaning1469 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause872 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1454 = false ∨ valuation q 1469 = true := counterClause872 (baseVal q)

theorem counterClause873 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1470)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 2 4 (meaning1400 q) (meaning1455 q) (meaning1470 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause873 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1455 = false ∨ valuation q 1470 = true := counterClause873 (baseVal q)

theorem counterClause874 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1471)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 2 5 (meaning1400 q) (meaning1456 q) (meaning1471 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause874 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1456 = false ∨ valuation q 1471 = true := counterClause874 (baseVal q)

theorem counterClause875 (q : Nat → Bool) : valuationOf q 1400 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1400)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1472)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 2 6 (meaning1400 q) (meaning1457 q) (meaning1472 q) hs
  change valuationOf q 1400 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause875 (q : Snake 81) (h : Conditions q) : valuation q 1400 = false ∨ valuation q 1457 = false ∨ valuation q 1472 = true := counterClause875 (baseVal q)

theorem counterClause876 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1401)) (literal (valuationOf q) (1467)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 3 (meaning1401 q) (meaning1467 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause876 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1467 = true := counterClause876 (baseVal q)

theorem counterClause877 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1468 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1468)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 3 1 (meaning1401 q) (meaning1452 q) (meaning1468 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause877 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1452 = false ∨ valuation q 1468 = true := counterClause877 (baseVal q)

theorem counterClause878 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1469 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1469)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 3 2 (meaning1401 q) (meaning1453 q) (meaning1469 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause878 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1453 = false ∨ valuation q 1469 = true := counterClause878 (baseVal q)

theorem counterClause879 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1470)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 3 3 (meaning1401 q) (meaning1454 q) (meaning1470 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause879 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1454 = false ∨ valuation q 1470 = true := counterClause879 (baseVal q)

theorem counterClause880 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1471)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 3 4 (meaning1401 q) (meaning1455 q) (meaning1471 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause880 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1455 = false ∨ valuation q 1471 = true := counterClause880 (baseVal q)

theorem counterClause881 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1472)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 3 5 (meaning1401 q) (meaning1456 q) (meaning1472 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause881 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1456 = false ∨ valuation q 1472 = true := counterClause881 (baseVal q)

theorem counterClause882 (q : Nat → Bool) : valuationOf q 1401 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1473 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1401)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1473)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 3 6 (meaning1401 q) (meaning1457 q) (meaning1473 q) hs
  change valuationOf q 1401 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause882 (q : Snake 81) (h : Conditions q) : valuation q 1401 = false ∨ valuation q 1457 = false ∨ valuation q 1473 = true := counterClause882 (baseVal q)

theorem counterClause883 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1469 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1469)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 4 1 (meaning1402 q) (meaning1452 q) (meaning1469 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause883 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1452 = false ∨ valuation q 1469 = true := counterClause883 (baseVal q)

theorem counterClause884 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1470)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 4 2 (meaning1402 q) (meaning1453 q) (meaning1470 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause884 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1453 = false ∨ valuation q 1470 = true := counterClause884 (baseVal q)

theorem counterClause885 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1471)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 4 3 (meaning1402 q) (meaning1454 q) (meaning1471 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause885 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1454 = false ∨ valuation q 1471 = true := counterClause885 (baseVal q)

theorem counterClause886 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1472)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 4 4 (meaning1402 q) (meaning1455 q) (meaning1472 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause886 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1455 = false ∨ valuation q 1472 = true := counterClause886 (baseVal q)

theorem counterClause887 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1473 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1456)) (literal (valuationOf q) (1473)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 4 5 (meaning1402 q) (meaning1456 q) (meaning1473 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1456 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause887 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1456 = false ∨ valuation q 1473 = true := counterClause887 (baseVal q)

theorem counterClause888 (q : Nat → Bool) : valuationOf q 1402 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1474 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1402)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1474)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 4 6 (meaning1402 q) (meaning1457 q) (meaning1474 q) hs
  change valuationOf q 1402 = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause888 (q : Snake 81) (h : Conditions q) : valuation q 1402 = false ∨ valuation q 1457 = false ∨ valuation q 1474 = true := counterClause888 (baseVal q)

theorem counterClause889 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1469 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_left (literal (valuationOf q) (1403)) (literal (valuationOf q) (1469)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 5 (meaning1403 q) (meaning1469 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause889 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1469 = true := counterClause889 (baseVal q)

theorem counterClause890 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1470 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1470)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 5 1 (meaning1403 q) (meaning1452 q) (meaning1470 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause890 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1452 = false ∨ valuation q 1470 = true := counterClause890 (baseVal q)

theorem counterClause891 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1471)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 5 2 (meaning1403 q) (meaning1453 q) (meaning1471 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause891 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1453 = false ∨ valuation q 1471 = true := counterClause891 (baseVal q)

theorem counterClause892 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1472)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 5 3 (meaning1403 q) (meaning1454 q) (meaning1472 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause892 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1454 = false ∨ valuation q 1472 = true := counterClause892 (baseVal q)

theorem counterClause893 (q : Nat → Bool) : valuationOf q 1403 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1473 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1403)) (literal (valuationOf q) (1455)) (literal (valuationOf q) (1473)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 5 4 (meaning1403 q) (meaning1455 q) (meaning1473 q) hs
  change valuationOf q 1403 = false ∨ valuationOf q 1455 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause893 (q : Snake 81) (h : Conditions q) : valuation q 1403 = false ∨ valuation q 1455 = false ∨ valuation q 1473 = true := counterClause893 (baseVal q)

theorem counterClause894 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1471 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1471)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 6 1 (meaning1404 q) (meaning1452 q) (meaning1471 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause894 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1452 = false ∨ valuation q 1471 = true := counterClause894 (baseVal q)

theorem counterClause895 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1472 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1472)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 6 2 (meaning1404 q) (meaning1453 q) (meaning1472 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause895 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1453 = false ∨ valuation q 1472 = true := counterClause895 (baseVal q)

theorem counterClause896 (q : Nat → Bool) : valuationOf q 1404 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1473 = true := by
  have hs : count1465 q = (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) + (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) := List.countP_append (p := literal q) (l₁ := [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (l₂ := [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105])
  have hm := merge_two (literal (valuationOf q) (1404)) (literal (valuationOf q) (1454)) (literal (valuationOf q) (1473)) (countLit q [-52, -53, -55, -57, -61, -62, -63, -65, -68, -70, -73, -75, -76]) (countLit q [-78, -81, -83, -85, -87, -89, -91, -93, -96, -98, -100, -102, -103, -105]) (count1465 q) 6 3 (meaning1404 q) (meaning1454 q) (meaning1473 q) hs
  change valuationOf q 1404 = false ∨ valuationOf q 1454 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause896 (q : Snake 81) (h : Conditions q) : valuation q 1404 = false ∨ valuation q 1454 = false ∨ valuation q 1473 = true := counterClause896 (baseVal q)

theorem block27 (q : Snake 81) (h : Conditions q) : B112E091.Block27 (valuation q) :=
  ⟨clause865 q h, clause866 q h, clause867 q h, clause868 q h, clause869 q h, clause870 q h, clause871 q h, clause872 q h, clause873 q h, clause874 q h, clause875 q h, clause876 q h, clause877 q h, clause878 q h, clause879 q h, clause880 q h, clause881 q h, clause882 q h, clause883 q h, clause884 q h, clause885 q h, clause886 q h, clause887 q h, clause888 q h, clause889 q h, clause890 q h, clause891 q h, clause892 q h, clause893 q h, clause894 q h, clause895 q h, clause896 q h⟩

end
end Snake9.Regrowth.E112091
