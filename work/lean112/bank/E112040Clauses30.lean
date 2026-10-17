import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_left (literal (valuationOf q) (1444)) (literal (valuationOf q) (1455)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 2 (meaning1444 q) (meaning1455 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1455 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1456)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 2 1 (meaning1444 q) (meaning1450 q) (meaning1456 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1450 = false ∨ valuation q 1456 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1457)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 2 2 (meaning1444 q) (meaning1451 q) (meaning1457 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1451 = false ∨ valuation q 1457 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1444 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_two (literal (valuationOf q) (1444)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1458)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 2 3 (meaning1444 q) (meaning1452 q) (meaning1458 q) hs
  change valuationOf q 1444 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1444 = false ∨ valuation q 1452 = false ∨ valuation q 1458 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_left (literal (valuationOf q) (1445)) (literal (valuationOf q) (1456)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 3 (meaning1445 q) (meaning1456 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1456 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1457)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 3 1 (meaning1445 q) (meaning1450 q) (meaning1457 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1450 = false ∨ valuation q 1457 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1445 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1458 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_two (literal (valuationOf q) (1445)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1458)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 3 2 (meaning1445 q) (meaning1451 q) (meaning1458 q) hs
  change valuationOf q 1445 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1445 = false ∨ valuation q 1451 = false ∨ valuation q 1458 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 18 = true ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_right (literal (valuationOf q) (-18)) (literal (valuationOf q) (1461)) (countLit q [-16]) (countLit q [-18]) (count1461 q) 1 (meaningNeg18 q) (meaning1461 q) hs
  change (! (valuationOf q 18)) = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 18 = true ∨ valuation q 1461 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 1461 = true := by
  have hs : count1461 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_left (literal (valuationOf q) (-16)) (literal (valuationOf q) (1461)) (countLit q [-16]) (countLit q [-18]) (count1461 q) 1 (meaningNeg16 q) (meaning1461 q) hs
  change (! (valuationOf q 16)) = false ∨ valuationOf q 1461 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 1461 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 16 = true ∨ valuationOf q 18 = true ∨ valuationOf q 1462 = true := by
  have hs : count1461 q = (countLit q [-16]) + (countLit q [-18]) := List.countP_append (p := literal q) (l₁ := [-16]) (l₂ := [-18])
  have hm := merge_two (literal (valuationOf q) (-16)) (literal (valuationOf q) (-18)) (literal (valuationOf q) (1462)) (countLit q [-16]) (countLit q [-18]) (count1461 q) 1 1 (meaningNeg16 q) (meaningNeg18 q) (meaning1462 q) hs
  change (! (valuationOf q 16)) = false ∨ (! (valuationOf q 18)) = false ∨ valuationOf q 1462 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 16 = true ∨ valuation q 18 = true ∨ valuation q 1462 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 22 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_right (literal (valuationOf q) (-22)) (literal (valuationOf q) (1463)) (countLit q [-21]) (countLit q [-22]) (count1463 q) 1 (meaningNeg22 q) (meaning1463 q) hs
  change (! (valuationOf q 22)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 22 = true ∨ valuation q 1463 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 1463 = true := by
  have hs : count1463 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_left (literal (valuationOf q) (-21)) (literal (valuationOf q) (1463)) (countLit q [-21]) (countLit q [-22]) (count1463 q) 1 (meaningNeg21 q) (meaning1463 q) hs
  change (! (valuationOf q 21)) = false ∨ valuationOf q 1463 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 1463 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 21 = true ∨ valuationOf q 22 = true ∨ valuationOf q 1464 = true := by
  have hs : count1463 q = (countLit q [-21]) + (countLit q [-22]) := List.countP_append (p := literal q) (l₁ := [-21]) (l₂ := [-22])
  have hm := merge_two (literal (valuationOf q) (-21)) (literal (valuationOf q) (-22)) (literal (valuationOf q) (1464)) (countLit q [-21]) (countLit q [-22]) (count1463 q) 1 1 (meaningNeg21 q) (meaningNeg22 q) (meaning1464 q) hs
  change (! (valuationOf q 21)) = false ∨ (! (valuationOf q 22)) = false ∨ valuationOf q 1464 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 21 = true ∨ valuation q 22 = true ∨ valuation q 1464 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1463 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-16, -18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-21, -22])
  have hm := merge_right (literal (valuationOf q) (1463)) (literal (valuationOf q) (1465)) (countLit q [-16, -18]) (countLit q [-21, -22]) (count1465 q) 1 (meaning1463 q) (meaning1465 q) hs
  change valuationOf q 1463 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1463 = false ∨ valuation q 1465 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1464 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-16, -18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-21, -22])
  have hm := merge_right (literal (valuationOf q) (1464)) (literal (valuationOf q) (1466)) (countLit q [-16, -18]) (countLit q [-21, -22]) (count1465 q) 2 (meaning1464 q) (meaning1466 q) hs
  change valuationOf q 1464 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1464 = false ∨ valuation q 1466 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1465 = true := by
  have hs : count1465 q = (countLit q [-16, -18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-21, -22])
  have hm := merge_left (literal (valuationOf q) (1461)) (literal (valuationOf q) (1465)) (countLit q [-16, -18]) (countLit q [-21, -22]) (count1465 q) 1 (meaning1461 q) (meaning1465 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1465 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1465 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-16, -18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1466)) (countLit q [-16, -18]) (countLit q [-21, -22]) (count1465 q) 1 1 (meaning1461 q) (meaning1463 q) (meaning1466 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1463 = false ∨ valuation q 1466 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1461 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-16, -18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (1461)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1467)) (countLit q [-16, -18]) (countLit q [-21, -22]) (count1465 q) 1 2 (meaning1461 q) (meaning1464 q) (meaning1467 q) hs
  change valuationOf q 1461 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1461 = false ∨ valuation q 1464 = false ∨ valuation q 1467 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1466 = true := by
  have hs : count1465 q = (countLit q [-16, -18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-21, -22])
  have hm := merge_left (literal (valuationOf q) (1462)) (literal (valuationOf q) (1466)) (countLit q [-16, -18]) (countLit q [-21, -22]) (count1465 q) 2 (meaning1462 q) (meaning1466 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1466 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1466 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1467 = true := by
  have hs : count1465 q = (countLit q [-16, -18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1463)) (literal (valuationOf q) (1467)) (countLit q [-16, -18]) (countLit q [-21, -22]) (count1465 q) 2 1 (meaning1462 q) (meaning1463 q) (meaning1467 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1463 = false ∨ valuationOf q 1467 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1463 = false ∨ valuation q 1467 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1468 = true := by
  have hs : count1465 q = (countLit q [-16, -18]) + (countLit q [-21, -22]) := List.countP_append (p := literal q) (l₁ := [-16, -18]) (l₂ := [-21, -22])
  have hm := merge_two (literal (valuationOf q) (1462)) (literal (valuationOf q) (1464)) (literal (valuationOf q) (1468)) (countLit q [-16, -18]) (countLit q [-21, -22]) (count1465 q) 2 2 (meaning1462 q) (meaning1464 q) (meaning1468 q) hs
  change valuationOf q 1462 = false ∨ valuationOf q 1464 = false ∨ valuationOf q 1468 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1462 = false ∨ valuation q 1464 = false ∨ valuation q 1468 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 26 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_right (literal (valuationOf q) (-26)) (literal (valuationOf q) (1469)) (countLit q [-24]) (countLit q [-26]) (count1469 q) 1 (meaningNeg26 q) (meaning1469 q) hs
  change (! (valuationOf q 26)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 26 = true ∨ valuation q 1469 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 1469 = true := by
  have hs : count1469 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_left (literal (valuationOf q) (-24)) (literal (valuationOf q) (1469)) (countLit q [-24]) (countLit q [-26]) (count1469 q) 1 (meaningNeg24 q) (meaning1469 q) hs
  change (! (valuationOf q 24)) = false ∨ valuationOf q 1469 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 1469 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 24 = true ∨ valuationOf q 26 = true ∨ valuationOf q 1470 = true := by
  have hs : count1469 q = (countLit q [-24]) + (countLit q [-26]) := List.countP_append (p := literal q) (l₁ := [-24]) (l₂ := [-26])
  have hm := merge_two (literal (valuationOf q) (-24)) (literal (valuationOf q) (-26)) (literal (valuationOf q) (1470)) (countLit q [-24]) (countLit q [-26]) (count1469 q) 1 1 (meaningNeg24 q) (meaningNeg26 q) (meaning1470 q) hs
  change (! (valuationOf q 24)) = false ∨ (! (valuationOf q 26)) = false ∨ valuationOf q 1470 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 24 = true ∨ valuation q 26 = true ∨ valuation q 1470 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 30 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_right (literal (valuationOf q) (-30)) (literal (valuationOf q) (1471)) (countLit q [-28]) (countLit q [-30]) (count1471 q) 1 (meaningNeg30 q) (meaning1471 q) hs
  change (! (valuationOf q 30)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 30 = true ∨ valuation q 1471 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 1471 = true := by
  have hs : count1471 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_left (literal (valuationOf q) (-28)) (literal (valuationOf q) (1471)) (countLit q [-28]) (countLit q [-30]) (count1471 q) 1 (meaningNeg28 q) (meaning1471 q) hs
  change (! (valuationOf q 28)) = false ∨ valuationOf q 1471 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 1471 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 28 = true ∨ valuationOf q 30 = true ∨ valuationOf q 1472 = true := by
  have hs : count1471 q = (countLit q [-28]) + (countLit q [-30]) := List.countP_append (p := literal q) (l₁ := [-28]) (l₂ := [-30])
  have hm := merge_two (literal (valuationOf q) (-28)) (literal (valuationOf q) (-30)) (literal (valuationOf q) (1472)) (countLit q [-28]) (countLit q [-30]) (count1471 q) 1 1 (meaningNeg28 q) (meaningNeg30 q) (meaning1472 q) hs
  change (! (valuationOf q 28)) = false ∨ (! (valuationOf q 30)) = false ∨ valuationOf q 1472 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 28 = true ∨ valuation q 30 = true ∨ valuation q 1472 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1471 = false ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (1471)) (literal (valuationOf q) (1473)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 1 (meaning1471 q) (meaning1473 q) hs
  change valuationOf q 1471 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1471 = false ∨ valuation q 1473 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1472 = false ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_right (literal (valuationOf q) (1472)) (literal (valuationOf q) (1474)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 2 (meaning1472 q) (meaning1474 q) hs
  change valuationOf q 1472 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1472 = false ∨ valuation q 1474 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1473 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_left (literal (valuationOf q) (1469)) (literal (valuationOf q) (1473)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 1 (meaning1469 q) (meaning1473 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1473 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1473 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1471)) (literal (valuationOf q) (1474)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 1 1 (meaning1469 q) (meaning1471 q) (meaning1474 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1471 = false ∨ valuationOf q 1474 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1471 = false ∨ valuation q 1474 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1469 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true := by
  have hs : count1473 q = (countLit q [-24, -26]) + (countLit q [-28, -30]) := List.countP_append (p := literal q) (l₁ := [-24, -26]) (l₂ := [-28, -30])
  have hm := merge_two (literal (valuationOf q) (1469)) (literal (valuationOf q) (1472)) (literal (valuationOf q) (1475)) (countLit q [-24, -26]) (countLit q [-28, -30]) (count1473 q) 1 2 (meaning1469 q) (meaning1472 q) (meaning1475 q) hs
  change valuationOf q 1469 = false ∨ valuationOf q 1472 = false ∨ valuationOf q 1475 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1469 = false ∨ valuation q 1472 = false ∨ valuation q 1475 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E040.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112040
