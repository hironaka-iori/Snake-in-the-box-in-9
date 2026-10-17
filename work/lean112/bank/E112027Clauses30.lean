import E112027Semantics
import B112E027Inputs
namespace Snake9.Regrowth.E112027
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_left (literal (valuationOf q) (1441)) (literal (valuationOf q) (1452)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 3 (meaning1441 q) (meaning1452 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1452 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1453 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1446)) (literal (valuationOf q) (1453)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 3 1 (meaning1441 q) (meaning1446 q) (meaning1453 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1446 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1446 = false ∨ valuation q 1453 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1454 = true := by
  have hs : count1450 q = (countLit q [-2, -3, -7]) + (countLit q [-8, -11, -13, -15]) := List.countP_append (p := literal q) (l₁ := [-2, -3, -7]) (l₂ := [-8, -11, -13, -15])
  have hm := merge_two (literal (valuationOf q) (1441)) (literal (valuationOf q) (1447)) (literal (valuationOf q) (1454)) (countLit q [-2, -3, -7]) (countLit q [-8, -11, -13, -15]) (count1450 q) 3 2 (meaning1441 q) (meaning1447 q) (meaning1454 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1447 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1447 = false ∨ valuation q 1454 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-19]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1457)) (countLit q [-19]) (countLit q [-22]) (count1457 q) 1 (meaningNeg22 q) (meaning1457 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1457 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 1457 = true := by
  have hs : count1457 q = (countLit q [-19]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-19)) (literal (valuationOf q) (1457)) (countLit q [-19]) (countLit q [-22]) (count1457 q) 1 (meaningNeg19 q) (meaning1457 q) hs
  change (! (valuationOf q 19)) = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 1457 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 19 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1458 = true := by
  have hs : count1457 q = (countLit q [-19]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-19]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-19)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1458)) (countLit q [-19]) (countLit q [-22]) (count1457 q) 1 1 (meaningNeg19 q) (meaningNeg22 q) (meaning1458 q) hs
  change (! (valuationOf q 19)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 19 = true ∨ valuation q 22 = true ∨ valuation q 1458 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1457 = false ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-17]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -22])
  have hm := merge_right (literal (valuationOf q) (1457)) (literal (valuationOf q) (1459)) (countLit q [-17]) (countLit q [-19, -22]) (count1459 q) 1 (meaning1457 q) (meaning1459 q) hs
  change valuationOf q 1457 = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1457 = false ∨ valuation q 1459 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1458 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-17]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -22])
  have hm := merge_right (literal (valuationOf q) (1458)) (literal (valuationOf q) (1460)) (countLit q [-17]) (countLit q [-19, -22]) (count1459 q) 2 (meaning1458 q) (meaning1460 q) hs
  change valuationOf q 1458 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1458 = false ∨ valuation q 1460 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1459 = true := by
  have hs : count1459 q = (countLit q [-17]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -22])
  have hm := merge_left (literal (valuationOf q) (-17)) (literal (valuationOf q) (1459)) (countLit q [-17]) (countLit q [-19, -22]) (count1459 q) 1 (meaningNeg17 q) (meaning1459 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1459 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1459 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true := by
  have hs : count1459 q = (countLit q [-17]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -22])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1457)) (literal (valuationOf q) (1460)) (countLit q [-17]) (countLit q [-19, -22]) (count1459 q) 1 1 (meaningNeg17 q) (meaning1457 q) (meaning1460 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1457 = false ∨ valuationOf q 1460 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1457 = false ∨ valuation q 1460 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 17 = true ∨ valuationOf q 1458 = false ∨ valuationOf q 1461 = true := by
  have hs : count1459 q = (countLit q [-17]) + (countLit q [-19, -22]) := List.countP_append (p := literal q) (l₁ := [-17]) (l₂ := [-19, -22])
  have hm := merge_two (literal (valuationOf q) (-17)) (literal (valuationOf q) (1458)) (literal (valuationOf q) (1461)) (countLit q [-17]) (countLit q [-19, -22]) (count1459 q) 1 2 (meaningNeg17 q) (meaning1458 q) (meaning1461 q) hs
  change (! (valuationOf q 17)) = false ∨ valuationOf q 1458 = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 17 = true ∨ valuation q 1458 = false ∨ valuation q 1461 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_right (literal (valuationOf q) (-24)) (literal (valuationOf q) (1462)) (countLit q [-23]) (countLit q [-24]) (count1462 q) 1 (meaningNeg24 q) (meaning1462 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1462 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 1462 = true := by
  have hs : count1462 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_left (literal (valuationOf q) (-23)) (literal (valuationOf q) (1462)) (countLit q [-23]) (countLit q [-24]) (count1462 q) 1 (meaningNeg23 q) (meaning1462 q) hs
  change (! (valuationOf q 23)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 1462 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 23 = true ∨ valuationOf q 24 = true ∨ valuationOf q 1463 = true := by
  have hs : count1462 q = (countLit q [-23]) + (countLit q [-24]) := List.countP_append (p := literal q) (l₁ := [-23]) (l₂ := [-24])
  have hm := merge_two (literal (valuationOf q) (-23)) (literal (valuationOf q) (-24)) (literal (valuationOf q) (1463)) (countLit q [-23]) (countLit q [-24]) (count1462 q) 1 1 (meaningNeg23 q) (meaningNeg24 q) (meaning1463 q) hs
  change (! (valuationOf q 23)) = false ∨ (! (valuationOf q 24)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 23 = true ∨ valuation q 24 = true ∨ valuation q 1463 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 29 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_right (literal (valuationOf q) (-29)) (literal (valuationOf q) (1464)) (countLit q [-27]) (countLit q [-29]) (count1464 q) 1 (meaningNeg29 q) (meaning1464 q) hs
  change (! (valuationOf q 29)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 29 = true ∨ valuation q 1464 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 1464 = true := by
  have hs : count1464 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_left (literal (valuationOf q) (-27)) (literal (valuationOf q) (1464)) (countLit q [-27]) (countLit q [-29]) (count1464 q) 1 (meaningNeg27 q) (meaning1464 q) hs
  change (! (valuationOf q 27)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 1464 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 27 = true ∨ valuationOf q 29 = true ∨ valuationOf q 1465 = true := by
  have hs : count1464 q = (countLit q [-27]) + (countLit q [-29]) := List.countP_append (p := literal q) (l₁ := [-27]) (l₂ := [-29])
  have hm := merge_two (literal (valuationOf q) (-27)) (literal (valuationOf q) (-29)) (literal (valuationOf q) (1465)) (countLit q [-27]) (countLit q [-29]) (count1464 q) 1 1 (meaningNeg27 q) (meaningNeg29 q) (meaning1465 q) hs
  change (! (valuationOf q 27)) = false ∨ (! (valuationOf q 29)) = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 27 = true ∨ valuation q 29 = true ∨ valuation q 1465 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1466 q) 1 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1465 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_right (literal (valuationOf q) (1465)) (literal (valuationOf q) (1467)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1466 q) 2 (meaning1465 q) (meaning1467 q) hs
  change valuationOf q 1465 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1465 = false ∨ valuation q 1467 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1466 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1466 q) 1 (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1466 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1466 q) 1 1 (meaning1462 q) (meaning1464 q) (meaning1467 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true := by
  have hs : count1466 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1465)) (literal (valuationOf q) (1468)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1466 q) 1 2 (meaning1462 q) (meaning1465 q) (meaning1468 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1465 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1465 = false ∨ valuation q 1468 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1466 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_left (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1466 q) 2 (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1467 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1466 q = (countLit q [-23, -24]) + (countLit q [-27, -29]) := List.countP_append (p := literal q) (l₁ := [-23, -24]) (l₂ := [-27, -29])
  have hm := merge_two (literal (valuationOf q) (1463)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-23, -24]) (countLit q [-27, -29]) (count1466 q) 2 1 (meaning1463 q) (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1464 = false ∨ valuation q 1468 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1466 = false ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-17, -19, -22]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1466)) (literal (valuationOf q) (1470)) (countLit q [-17, -19, -22]) (countLit q [-23, -24, -27, -29]) (count1470 q) 1 (meaning1466 q) (meaning1470 q) hs
  change valuationOf q 1466 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1466 = false ∨ valuation q 1470 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1467 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-17, -19, -22]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1467)) (literal (valuationOf q) (1471)) (countLit q [-17, -19, -22]) (countLit q [-23, -24, -27, -29]) (count1470 q) 2 (meaning1467 q) (meaning1471 q) hs
  change valuationOf q 1467 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1467 = false ∨ valuation q 1471 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1468 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-17, -19, -22]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_right (literal (valuationOf q) (1468)) (literal (valuationOf q) (1472)) (countLit q [-17, -19, -22]) (countLit q [-23, -24, -27, -29]) (count1470 q) 3 (meaning1468 q) (meaning1472 q) hs
  change valuationOf q 1468 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1468 = false ∨ valuation q 1472 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1470 = true := by
  have hs : count1470 q = (countLit q [-17, -19, -22]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1459)) (literal (valuationOf q) (1470)) (countLit q [-17, -19, -22]) (countLit q [-23, -24, -27, -29]) (count1470 q) 1 (meaning1459 q) (meaning1470 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1470 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-17, -19, -22]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1466)) (literal (valuationOf q) (1471)) (countLit q [-17, -19, -22]) (countLit q [-23, -24, -27, -29]) (count1470 q) 1 1 (meaning1459 q) (meaning1466 q) (meaning1471 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1466 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1466 = false ∨ valuation q 1471 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true := by
  have hs : count1470 q = (countLit q [-17, -19, -22]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1467)) (literal (valuationOf q) (1472)) (countLit q [-17, -19, -22]) (countLit q [-23, -24, -27, -29]) (count1470 q) 1 2 (meaning1459 q) (meaning1467 q) (meaning1472 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1467 = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1467 = false ∨ valuation q 1472 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1459 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1473 = true := by
  have hs : count1470 q = (countLit q [-17, -19, -22]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_two (literal (valuationOf q) (1459)) (literal (valuationOf q) (1468)) (literal (valuationOf q) (1473)) (countLit q [-17, -19, -22]) (countLit q [-23, -24, -27, -29]) (count1470 q) 1 3 (meaning1459 q) (meaning1468 q) (meaning1473 q) hs
  change valuationOf q 1459 = false ∨ valuationOf q 1468 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1459 = false ∨ valuation q 1468 = false ∨ valuation q 1473 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1460 = false ∨ valuationOf q 1471 = true := by
  have hs : count1470 q = (countLit q [-17, -19, -22]) + (countLit q [-23, -24, -27, -29]) := List.countP_append (p := literal q) (l₁ := [-17, -19, -22]) (l₂ := [-23, -24, -27, -29])
  have hm := merge_left (literal (valuationOf q) (1460)) (literal (valuationOf q) (1471)) (countLit q [-17, -19, -22]) (countLit q [-23, -24, -27, -29]) (count1470 q) 2 (meaning1460 q) (meaning1471 q) hs
  change valuationOf q 1460 = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1460 = false ∨ valuation q 1471 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E027.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112027
