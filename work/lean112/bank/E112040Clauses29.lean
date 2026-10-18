import E112040Semantics
import B112E040Inputs
namespace Snake9.Regrowth.E112040
noncomputable section
local instance blockDec29 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem clause929 (q : Snake 81) (h : Conditions q) : valuation q 1096 = false := by
  rw [value1096]
  simp only [decide_eq_true_eq, decide_eq_false_iff_not]
  have he : count1078 (baseVal q) = (evenSide.filter (fun v => !(decide (InPath q v)))).length := by
    rw [← List.countP_eq_length_filter]
    rfl
  have hb := absent_even_bound q h
  rw [evenSide_length] at hb
  rw [he]
  omega

theorem counterClause930 (q : Nat → Bool) : valuationOf q 6 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_right (literal (valuationOf q) (-6)) (literal (valuationOf q) (1441)) (countLit q [-4]) (countLit q [-6]) (count1441 q) 1 (meaningNeg6 q) (meaning1441 q) hs
  change (! (valuationOf q 6)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause930 (q : Snake 81) (h : Conditions q) : valuation q 6 = true ∨ valuation q 1441 = true := counterClause930 (baseVal q)

theorem counterClause931 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 1441 = true := by
  have hs : count1441 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_left (literal (valuationOf q) (-4)) (literal (valuationOf q) (1441)) (countLit q [-4]) (countLit q [-6]) (count1441 q) 1 (meaningNeg4 q) (meaning1441 q) hs
  change (! (valuationOf q 4)) = false ∨ valuationOf q 1441 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause931 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 1441 = true := counterClause931 (baseVal q)

theorem counterClause932 (q : Nat → Bool) : valuationOf q 4 = true ∨ valuationOf q 6 = true ∨ valuationOf q 1442 = true := by
  have hs : count1441 q = (countLit q [-4]) + (countLit q [-6]) := List.countP_append (p := literal q) (l₁ := [-4]) (l₂ := [-6])
  have hm := merge_two (literal (valuationOf q) (-4)) (literal (valuationOf q) (-6)) (literal (valuationOf q) (1442)) (countLit q [-4]) (countLit q [-6]) (count1441 q) 1 1 (meaningNeg4 q) (meaningNeg6 q) (meaning1442 q) hs
  change (! (valuationOf q 4)) = false ∨ (! (valuationOf q 6)) = false ∨ valuationOf q 1442 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause932 (q : Snake 81) (h : Conditions q) : valuation q 4 = true ∨ valuation q 6 = true ∨ valuation q 1442 = true := counterClause932 (baseVal q)

theorem counterClause933 (q : Nat → Bool) : valuationOf q 1441 = false ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (1441)) (literal (valuationOf q) (1443)) (countLit q [-3]) (countLit q [-4, -6]) (count1443 q) 1 (meaning1441 q) (meaning1443 q) hs
  change valuationOf q 1441 = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause933 (q : Snake 81) (h : Conditions q) : valuation q 1441 = false ∨ valuation q 1443 = true := counterClause933 (baseVal q)

theorem counterClause934 (q : Nat → Bool) : valuationOf q 1442 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_right (literal (valuationOf q) (1442)) (literal (valuationOf q) (1444)) (countLit q [-3]) (countLit q [-4, -6]) (count1443 q) 2 (meaning1442 q) (meaning1444 q) hs
  change valuationOf q 1442 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause934 (q : Snake 81) (h : Conditions q) : valuation q 1442 = false ∨ valuation q 1444 = true := counterClause934 (baseVal q)

theorem counterClause935 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1443 = true := by
  have hs : count1443 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_left (literal (valuationOf q) (-3)) (literal (valuationOf q) (1443)) (countLit q [-3]) (countLit q [-4, -6]) (count1443 q) 1 (meaningNeg3 q) (meaning1443 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1443 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause935 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1443 = true := counterClause935 (baseVal q)

theorem counterClause936 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true := by
  have hs : count1443 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1441)) (literal (valuationOf q) (1444)) (countLit q [-3]) (countLit q [-4, -6]) (count1443 q) 1 1 (meaningNeg3 q) (meaning1441 q) (meaning1444 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1441 = false ∨ valuationOf q 1444 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause936 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1441 = false ∨ valuation q 1444 = true := counterClause936 (baseVal q)

theorem counterClause937 (q : Nat → Bool) : valuationOf q 3 = true ∨ valuationOf q 1442 = false ∨ valuationOf q 1445 = true := by
  have hs : count1443 q = (countLit q [-3]) + (countLit q [-4, -6]) := List.countP_append (p := literal q) (l₁ := [-3]) (l₂ := [-4, -6])
  have hm := merge_two (literal (valuationOf q) (-3)) (literal (valuationOf q) (1442)) (literal (valuationOf q) (1445)) (countLit q [-3]) (countLit q [-4, -6]) (count1443 q) 1 2 (meaningNeg3 q) (meaning1442 q) (meaning1445 q) hs
  change (! (valuationOf q 3)) = false ∨ valuationOf q 1442 = false ∨ valuationOf q 1445 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause937 (q : Snake 81) (h : Conditions q) : valuation q 3 = true ∨ valuation q 1442 = false ∨ valuation q 1445 = true := counterClause937 (baseVal q)

theorem counterClause938 (q : Nat → Bool) : valuationOf q 9 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-7]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9])
  have hm := merge_right (literal (valuationOf q) (-9)) (literal (valuationOf q) (1446)) (countLit q [-7]) (countLit q [-9]) (count1446 q) 1 (meaningNeg9 q) (meaning1446 q) hs
  change (! (valuationOf q 9)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause938 (q : Snake 81) (h : Conditions q) : valuation q 9 = true ∨ valuation q 1446 = true := counterClause938 (baseVal q)

theorem counterClause939 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 1446 = true := by
  have hs : count1446 q = (countLit q [-7]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9])
  have hm := merge_left (literal (valuationOf q) (-7)) (literal (valuationOf q) (1446)) (countLit q [-7]) (countLit q [-9]) (count1446 q) 1 (meaningNeg7 q) (meaning1446 q) hs
  change (! (valuationOf q 7)) = false ∨ valuationOf q 1446 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause939 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 1446 = true := counterClause939 (baseVal q)

theorem counterClause940 (q : Nat → Bool) : valuationOf q 7 = true ∨ valuationOf q 9 = true ∨ valuationOf q 1447 = true := by
  have hs : count1446 q = (countLit q [-7]) + (countLit q [-9]) := List.countP_append (p := literal q) (l₁ := [-7]) (l₂ := [-9])
  have hm := merge_two (literal (valuationOf q) (-7)) (literal (valuationOf q) (-9)) (literal (valuationOf q) (1447)) (countLit q [-7]) (countLit q [-9]) (count1446 q) 1 1 (meaningNeg7 q) (meaningNeg9 q) (meaning1447 q) hs
  change (! (valuationOf q 7)) = false ∨ (! (valuationOf q 9)) = false ∨ valuationOf q 1447 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause940 (q : Snake 81) (h : Conditions q) : valuation q 7 = true ∨ valuation q 9 = true ∨ valuation q 1447 = true := counterClause940 (baseVal q)

theorem counterClause941 (q : Nat → Bool) : valuationOf q 15 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-12]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-15])
  have hm := merge_right (literal (valuationOf q) (-15)) (literal (valuationOf q) (1448)) (countLit q [-12]) (countLit q [-15]) (count1448 q) 1 (meaningNeg15 q) (meaning1448 q) hs
  change (! (valuationOf q 15)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause941 (q : Snake 81) (h : Conditions q) : valuation q 15 = true ∨ valuation q 1448 = true := counterClause941 (baseVal q)

theorem counterClause942 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 1448 = true := by
  have hs : count1448 q = (countLit q [-12]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-15])
  have hm := merge_left (literal (valuationOf q) (-12)) (literal (valuationOf q) (1448)) (countLit q [-12]) (countLit q [-15]) (count1448 q) 1 (meaningNeg12 q) (meaning1448 q) hs
  change (! (valuationOf q 12)) = false ∨ valuationOf q 1448 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause942 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 1448 = true := counterClause942 (baseVal q)

theorem counterClause943 (q : Nat → Bool) : valuationOf q 12 = true ∨ valuationOf q 15 = true ∨ valuationOf q 1449 = true := by
  have hs : count1448 q = (countLit q [-12]) + (countLit q [-15]) := List.countP_append (p := literal q) (l₁ := [-12]) (l₂ := [-15])
  have hm := merge_two (literal (valuationOf q) (-12)) (literal (valuationOf q) (-15)) (literal (valuationOf q) (1449)) (countLit q [-12]) (countLit q [-15]) (count1448 q) 1 1 (meaningNeg12 q) (meaningNeg15 q) (meaning1449 q) hs
  change (! (valuationOf q 12)) = false ∨ (! (valuationOf q 15)) = false ∨ valuationOf q 1449 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause943 (q : Snake 81) (h : Conditions q) : valuation q 12 = true ∨ valuation q 15 = true ∨ valuation q 1449 = true := counterClause943 (baseVal q)

theorem counterClause944 (q : Nat → Bool) : valuationOf q 1448 = false ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-7, -9]) + (countLit q [-12, -15]) := List.countP_append (p := literal q) (l₁ := [-7, -9]) (l₂ := [-12, -15])
  have hm := merge_right (literal (valuationOf q) (1448)) (literal (valuationOf q) (1450)) (countLit q [-7, -9]) (countLit q [-12, -15]) (count1450 q) 1 (meaning1448 q) (meaning1450 q) hs
  change valuationOf q 1448 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause944 (q : Snake 81) (h : Conditions q) : valuation q 1448 = false ∨ valuation q 1450 = true := counterClause944 (baseVal q)

theorem counterClause945 (q : Nat → Bool) : valuationOf q 1449 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-7, -9]) + (countLit q [-12, -15]) := List.countP_append (p := literal q) (l₁ := [-7, -9]) (l₂ := [-12, -15])
  have hm := merge_right (literal (valuationOf q) (1449)) (literal (valuationOf q) (1451)) (countLit q [-7, -9]) (countLit q [-12, -15]) (count1450 q) 2 (meaning1449 q) (meaning1451 q) hs
  change valuationOf q 1449 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause945 (q : Snake 81) (h : Conditions q) : valuation q 1449 = false ∨ valuation q 1451 = true := counterClause945 (baseVal q)

theorem counterClause946 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1450 = true := by
  have hs : count1450 q = (countLit q [-7, -9]) + (countLit q [-12, -15]) := List.countP_append (p := literal q) (l₁ := [-7, -9]) (l₂ := [-12, -15])
  have hm := merge_left (literal (valuationOf q) (1446)) (literal (valuationOf q) (1450)) (countLit q [-7, -9]) (countLit q [-12, -15]) (count1450 q) 1 (meaning1446 q) (meaning1450 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1450 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause946 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1450 = true := counterClause946 (baseVal q)

theorem counterClause947 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-7, -9]) + (countLit q [-12, -15]) := List.countP_append (p := literal q) (l₁ := [-7, -9]) (l₂ := [-12, -15])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1451)) (countLit q [-7, -9]) (countLit q [-12, -15]) (count1450 q) 1 1 (meaning1446 q) (meaning1448 q) (meaning1451 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause947 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1448 = false ∨ valuation q 1451 = true := counterClause947 (baseVal q)

theorem counterClause948 (q : Nat → Bool) : valuationOf q 1446 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-7, -9]) + (countLit q [-12, -15]) := List.countP_append (p := literal q) (l₁ := [-7, -9]) (l₂ := [-12, -15])
  have hm := merge_two (literal (valuationOf q) (1446)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1452)) (countLit q [-7, -9]) (countLit q [-12, -15]) (count1450 q) 1 2 (meaning1446 q) (meaning1449 q) (meaning1452 q) hs
  change valuationOf q 1446 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause948 (q : Snake 81) (h : Conditions q) : valuation q 1446 = false ∨ valuation q 1449 = false ∨ valuation q 1452 = true := counterClause948 (baseVal q)

theorem counterClause949 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1451 = true := by
  have hs : count1450 q = (countLit q [-7, -9]) + (countLit q [-12, -15]) := List.countP_append (p := literal q) (l₁ := [-7, -9]) (l₂ := [-12, -15])
  have hm := merge_left (literal (valuationOf q) (1447)) (literal (valuationOf q) (1451)) (countLit q [-7, -9]) (countLit q [-12, -15]) (count1450 q) 2 (meaning1447 q) (meaning1451 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1451 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause949 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1451 = true := counterClause949 (baseVal q)

theorem counterClause950 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true := by
  have hs : count1450 q = (countLit q [-7, -9]) + (countLit q [-12, -15]) := List.countP_append (p := literal q) (l₁ := [-7, -9]) (l₂ := [-12, -15])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1448)) (literal (valuationOf q) (1452)) (countLit q [-7, -9]) (countLit q [-12, -15]) (count1450 q) 2 1 (meaning1447 q) (meaning1448 q) (meaning1452 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1448 = false ∨ valuationOf q 1452 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause950 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1448 = false ∨ valuation q 1452 = true := counterClause950 (baseVal q)

theorem counterClause951 (q : Nat → Bool) : valuationOf q 1447 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1453 = true := by
  have hs : count1450 q = (countLit q [-7, -9]) + (countLit q [-12, -15]) := List.countP_append (p := literal q) (l₁ := [-7, -9]) (l₂ := [-12, -15])
  have hm := merge_two (literal (valuationOf q) (1447)) (literal (valuationOf q) (1449)) (literal (valuationOf q) (1453)) (countLit q [-7, -9]) (countLit q [-12, -15]) (count1450 q) 2 2 (meaning1447 q) (meaning1449 q) (meaning1453 q) hs
  change valuationOf q 1447 = false ∨ valuationOf q 1449 = false ∨ valuationOf q 1453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause951 (q : Snake 81) (h : Conditions q) : valuation q 1447 = false ∨ valuation q 1449 = false ∨ valuation q 1453 = true := counterClause951 (baseVal q)

theorem counterClause952 (q : Nat → Bool) : valuationOf q 1450 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_right (literal (valuationOf q) (1450)) (literal (valuationOf q) (1454)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 1 (meaning1450 q) (meaning1454 q) hs
  change valuationOf q 1450 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause952 (q : Snake 81) (h : Conditions q) : valuation q 1450 = false ∨ valuation q 1454 = true := counterClause952 (baseVal q)

theorem counterClause953 (q : Nat → Bool) : valuationOf q 1451 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_right (literal (valuationOf q) (1451)) (literal (valuationOf q) (1455)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 2 (meaning1451 q) (meaning1455 q) hs
  change valuationOf q 1451 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause953 (q : Snake 81) (h : Conditions q) : valuation q 1451 = false ∨ valuation q 1455 = true := counterClause953 (baseVal q)

theorem counterClause954 (q : Nat → Bool) : valuationOf q 1452 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_right (literal (valuationOf q) (1452)) (literal (valuationOf q) (1456)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 3 (meaning1452 q) (meaning1456 q) hs
  change valuationOf q 1452 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause954 (q : Snake 81) (h : Conditions q) : valuation q 1452 = false ∨ valuation q 1456 = true := counterClause954 (baseVal q)

theorem counterClause955 (q : Nat → Bool) : valuationOf q 1453 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_right (literal (valuationOf q) (1453)) (literal (valuationOf q) (1457)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 4 (meaning1453 q) (meaning1457 q) hs
  change valuationOf q 1453 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause955 (q : Snake 81) (h : Conditions q) : valuation q 1453 = false ∨ valuation q 1457 = true := counterClause955 (baseVal q)

theorem counterClause956 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1454 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_left (literal (valuationOf q) (1443)) (literal (valuationOf q) (1454)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 1 (meaning1443 q) (meaning1454 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1454 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause956 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1454 = true := counterClause956 (baseVal q)

theorem counterClause957 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1450)) (literal (valuationOf q) (1455)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 1 1 (meaning1443 q) (meaning1450 q) (meaning1455 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1450 = false ∨ valuationOf q 1455 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause957 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1450 = false ∨ valuation q 1455 = true := counterClause957 (baseVal q)

theorem counterClause958 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1451)) (literal (valuationOf q) (1456)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 1 2 (meaning1443 q) (meaning1451 q) (meaning1456 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1451 = false ∨ valuationOf q 1456 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause958 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1451 = false ∨ valuation q 1456 = true := counterClause958 (baseVal q)

theorem counterClause959 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1452)) (literal (valuationOf q) (1457)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 1 3 (meaning1443 q) (meaning1452 q) (meaning1457 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1452 = false ∨ valuationOf q 1457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause959 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1452 = false ∨ valuation q 1457 = true := counterClause959 (baseVal q)

theorem counterClause960 (q : Nat → Bool) : valuationOf q 1443 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true := by
  have hs : count1454 q = (countLit q [-3, -4, -6]) + (countLit q [-7, -9, -12, -15]) := List.countP_append (p := literal q) (l₁ := [-3, -4, -6]) (l₂ := [-7, -9, -12, -15])
  have hm := merge_two (literal (valuationOf q) (1443)) (literal (valuationOf q) (1453)) (literal (valuationOf q) (1458)) (countLit q [-3, -4, -6]) (countLit q [-7, -9, -12, -15]) (count1454 q) 1 4 (meaning1443 q) (meaning1453 q) (meaning1458 q) hs
  change valuationOf q 1443 = false ∨ valuationOf q 1453 = false ∨ valuationOf q 1458 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause960 (q : Snake 81) (h : Conditions q) : valuation q 1443 = false ∨ valuation q 1453 = false ∨ valuation q 1458 = true := counterClause960 (baseVal q)

theorem block29 (q : Snake 81) (h : Conditions q) : B112E040.Block29 (valuation q) :=
  ⟨clause929 q h, clause930 q h, clause931 q h, clause932 q h, clause933 q h, clause934 q h, clause935 q h, clause936 q h, clause937 q h, clause938 q h, clause939 q h, clause940 q h, clause941 q h, clause942 q h, clause943 q h, clause944 q h, clause945 q h, clause946 q h, clause947 q h, clause948 q h, clause949 q h, clause950 q h, clause951 q h, clause952 q h, clause953 q h, clause954 q h, clause955 q h, clause956 q h, clause957 q h, clause958 q h, clause959 q h, clause960 q h⟩

end
end Snake9.Regrowth.E112040
