import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-65, -67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -70])
  have hm := merge_two (literal (valuationOf q) (1531)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1536)) (countLit q [-65, -67]) (countLit q [-69, -70]) (count1535 q) 1 1 (meaning1531 q) (meaning1533 q) (meaning1536 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1533 = false ∨ valuation q 1536 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1532 = false ∨ valuationOf q 1536 = true := by
  have hs : count1535 q = (countLit q [-65, -67]) + (countLit q [-69, -70]) := List.countP_append (p := literal q) (l₁ := [-65, -67]) (l₂ := [-69, -70])
  have hm := merge_left (literal (valuationOf q) (1532)) (literal (valuationOf q) (1536)) (countLit q [-65, -67]) (countLit q [-69, -70]) (count1535 q) 2 (meaning1532 q) (meaning1536 q) hs
  change valuationOf q 1532 = false ∨ valuationOf q 1536 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1532 = false ∨ valuation q 1536 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 1535 = false ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-57, -59, -63]) + (countLit q [-65, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63]) (l₂ := [-65, -67, -69, -70])
  have hm := merge_right (literal (valuationOf q) (1535)) (literal (valuationOf q) (1539)) (countLit q [-57, -59, -63]) (countLit q [-65, -67, -69, -70]) (count1539 q) 1 (meaning1535 q) (meaning1539 q) hs
  change valuationOf q 1535 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 1535 = false ∨ valuation q 1539 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 1536 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-57, -59, -63]) + (countLit q [-65, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63]) (l₂ := [-65, -67, -69, -70])
  have hm := merge_right (literal (valuationOf q) (1536)) (literal (valuationOf q) (1540)) (countLit q [-57, -59, -63]) (countLit q [-65, -67, -69, -70]) (count1539 q) 2 (meaning1536 q) (meaning1540 q) hs
  change valuationOf q 1536 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 1536 = false ∨ valuation q 1540 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1539 = true := by
  have hs : count1539 q = (countLit q [-57, -59, -63]) + (countLit q [-65, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63]) (l₂ := [-65, -67, -69, -70])
  have hm := merge_left (literal (valuationOf q) (1528)) (literal (valuationOf q) (1539)) (countLit q [-57, -59, -63]) (countLit q [-65, -67, -69, -70]) (count1539 q) 1 (meaning1528 q) (meaning1539 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1539 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-57, -59, -63]) + (countLit q [-65, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63]) (l₂ := [-65, -67, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1540)) (countLit q [-57, -59, -63]) (countLit q [-65, -67, -69, -70]) (count1539 q) 1 1 (meaning1528 q) (meaning1535 q) (meaning1540 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1535 = false ∨ valuation q 1540 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 1528 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-57, -59, -63]) + (countLit q [-65, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63]) (l₂ := [-65, -67, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1528)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1541)) (countLit q [-57, -59, -63]) (countLit q [-65, -67, -69, -70]) (count1539 q) 1 2 (meaning1528 q) (meaning1536 q) (meaning1541 q) hs
  change valuationOf q 1528 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 1528 = false ∨ valuation q 1536 = false ∨ valuation q 1541 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1540 = true := by
  have hs : count1539 q = (countLit q [-57, -59, -63]) + (countLit q [-65, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63]) (l₂ := [-65, -67, -69, -70])
  have hm := merge_left (literal (valuationOf q) (1529)) (literal (valuationOf q) (1540)) (countLit q [-57, -59, -63]) (countLit q [-65, -67, -69, -70]) (count1539 q) 2 (meaning1529 q) (meaning1540 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1540 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true := by
  have hs : count1539 q = (countLit q [-57, -59, -63]) + (countLit q [-65, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63]) (l₂ := [-65, -67, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1535)) (literal (valuationOf q) (1541)) (countLit q [-57, -59, -63]) (countLit q [-65, -67, -69, -70]) (count1539 q) 2 1 (meaning1529 q) (meaning1535 q) (meaning1541 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1535 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1535 = false ∨ valuation q 1541 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1529 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1542 = true := by
  have hs : count1539 q = (countLit q [-57, -59, -63]) + (countLit q [-65, -67, -69, -70]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63]) (l₂ := [-65, -67, -69, -70])
  have hm := merge_two (literal (valuationOf q) (1529)) (literal (valuationOf q) (1536)) (literal (valuationOf q) (1542)) (countLit q [-57, -59, -63]) (countLit q [-65, -67, -69, -70]) (count1539 q) 2 2 (meaning1529 q) (meaning1536 q) (meaning1542 q) hs
  change valuationOf q 1529 = false ∨ valuationOf q 1536 = false ∨ valuationOf q 1542 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1529 = false ∨ valuation q 1536 = false ∨ valuation q 1542 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 77 = true ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_right (literal (valuationOf q) (-77)) (literal (valuationOf q) (1546)) (countLit q [-75]) (countLit q [-77]) (count1546 q) 1 (meaningNeg77 q) (meaning1546 q) hs
  change (! (valuationOf q 77)) = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 77 = true ∨ valuation q 1546 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 1546 = true := by
  have hs : count1546 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_left (literal (valuationOf q) (-75)) (literal (valuationOf q) (1546)) (countLit q [-75]) (countLit q [-77]) (count1546 q) 1 (meaningNeg75 q) (meaning1546 q) hs
  change (! (valuationOf q 75)) = false ∨ valuationOf q 1546 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 1546 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 75 = true ∨ valuationOf q 77 = true ∨ valuationOf q 1547 = true := by
  have hs : count1546 q = (countLit q [-75]) + (countLit q [-77]) := List.countP_append (p := literal q) (l₁ := [-75]) (l₂ := [-77])
  have hm := merge_two (literal (valuationOf q) (-75)) (literal (valuationOf q) (-77)) (literal (valuationOf q) (1547)) (countLit q [-75]) (countLit q [-77]) (count1546 q) 1 1 (meaningNeg75 q) (meaningNeg77 q) (meaning1547 q) hs
  change (! (valuationOf q 75)) = false ∨ (! (valuationOf q 77)) = false ∨ valuationOf q 1547 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 75 = true ∨ valuation q 77 = true ∨ valuation q 1547 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1546 = false ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-72]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-75, -77])
  have hm := merge_right (literal (valuationOf q) (1546)) (literal (valuationOf q) (1548)) (countLit q [-72]) (countLit q [-75, -77]) (count1548 q) 1 (meaning1546 q) (meaning1548 q) hs
  change valuationOf q 1546 = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1546 = false ∨ valuation q 1548 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1547 = false ∨ valuationOf q 1549 = true := by
  have hs : count1548 q = (countLit q [-72]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-75, -77])
  have hm := merge_right (literal (valuationOf q) (1547)) (literal (valuationOf q) (1549)) (countLit q [-72]) (countLit q [-75, -77]) (count1548 q) 2 (meaning1547 q) (meaning1549 q) hs
  change valuationOf q 1547 = false ∨ valuationOf q 1549 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1547 = false ∨ valuation q 1549 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1548 = true := by
  have hs : count1548 q = (countLit q [-72]) + (countLit q [-75, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-75, -77])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1548)) (countLit q [-72]) (countLit q [-75, -77]) (count1548 q) 1 (meaningNeg72 q) (meaning1548 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1548 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1548 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 80 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_right (literal (valuationOf q) (-80)) (literal (valuationOf q) (1551)) (countLit q [-78]) (countLit q [-80]) (count1551 q) 1 (meaningNeg80 q) (meaning1551 q) hs
  change (! (valuationOf q 80)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 80 = true ∨ valuation q 1551 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1551 = true := by
  have hs : count1551 q = (countLit q [-78]) + (countLit q [-80]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-80])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1551)) (countLit q [-78]) (countLit q [-80]) (count1551 q) 1 (meaningNeg78 q) (meaning1551 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1551 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1551 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1553)) (countLit q [-83]) (countLit q [-85]) (count1553 q) 1 (meaningNeg85 q) (meaning1553 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1553 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 1553 = true := by
  have hs : count1553 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-83)) (literal (valuationOf q) (1553)) (countLit q [-83]) (countLit q [-85]) (count1553 q) 1 (meaningNeg83 q) (meaning1553 q) hs
  change (! (valuationOf q 83)) = false ∨ valuationOf q 1553 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 1553 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 83 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1554 = true := by
  have hs : count1553 q = (countLit q [-83]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-83]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-83)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1554)) (countLit q [-83]) (countLit q [-85]) (count1553 q) 1 1 (meaningNeg83 q) (meaningNeg85 q) (meaning1554 q) hs
  change (! (valuationOf q 83)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1554 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 83 = true ∨ valuation q 85 = true ∨ valuation q 1554 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1553 = false ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-78, -80]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-83, -85])
  have hm := merge_right (literal (valuationOf q) (1553)) (literal (valuationOf q) (1555)) (countLit q [-78, -80]) (countLit q [-83, -85]) (count1555 q) 1 (meaning1553 q) (meaning1555 q) hs
  change valuationOf q 1553 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1553 = false ∨ valuation q 1555 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1554 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-78, -80]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-83, -85])
  have hm := merge_right (literal (valuationOf q) (1554)) (literal (valuationOf q) (1556)) (countLit q [-78, -80]) (countLit q [-83, -85]) (count1555 q) 2 (meaning1554 q) (meaning1556 q) hs
  change valuationOf q 1554 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1554 = false ∨ valuation q 1556 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1555 = true := by
  have hs : count1555 q = (countLit q [-78, -80]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-83, -85])
  have hm := merge_left (literal (valuationOf q) (1551)) (literal (valuationOf q) (1555)) (countLit q [-78, -80]) (countLit q [-83, -85]) (count1555 q) 1 (meaning1551 q) (meaning1555 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1555 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1555 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1551 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1556 = true := by
  have hs : count1555 q = (countLit q [-78, -80]) + (countLit q [-83, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -80]) (l₂ := [-83, -85])
  have hm := merge_two (literal (valuationOf q) (1551)) (literal (valuationOf q) (1553)) (literal (valuationOf q) (1556)) (countLit q [-78, -80]) (countLit q [-83, -85]) (count1555 q) 1 1 (meaning1551 q) (meaning1553 q) (meaning1556 q) hs
  change valuationOf q 1551 = false ∨ valuationOf q 1553 = false ∨ valuationOf q 1556 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1551 = false ∨ valuation q 1553 = false ∨ valuation q 1556 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1555 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-72, -75, -77]) + (countLit q [-78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -75, -77]) (l₂ := [-78, -80, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1555)) (literal (valuationOf q) (1559)) (countLit q [-72, -75, -77]) (countLit q [-78, -80, -83, -85]) (count1559 q) 1 (meaning1555 q) (meaning1559 q) hs
  change valuationOf q 1555 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1555 = false ∨ valuation q 1559 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1556 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-72, -75, -77]) + (countLit q [-78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -75, -77]) (l₂ := [-78, -80, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1556)) (literal (valuationOf q) (1560)) (countLit q [-72, -75, -77]) (countLit q [-78, -80, -83, -85]) (count1559 q) 2 (meaning1556 q) (meaning1560 q) hs
  change valuationOf q 1556 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1556 = false ∨ valuation q 1560 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1559 = true := by
  have hs : count1559 q = (countLit q [-72, -75, -77]) + (countLit q [-78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -75, -77]) (l₂ := [-78, -80, -83, -85])
  have hm := merge_left (literal (valuationOf q) (1548)) (literal (valuationOf q) (1559)) (countLit q [-72, -75, -77]) (countLit q [-78, -80, -83, -85]) (count1559 q) 1 (meaning1548 q) (meaning1559 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1559 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1559 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1560 = true := by
  have hs : count1559 q = (countLit q [-72, -75, -77]) + (countLit q [-78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -75, -77]) (l₂ := [-78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1560)) (countLit q [-72, -75, -77]) (countLit q [-78, -80, -83, -85]) (count1559 q) 1 1 (meaning1548 q) (meaning1555 q) (meaning1560 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1560 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1555 = false ∨ valuation q 1560 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1548 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-72, -75, -77]) + (countLit q [-78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -75, -77]) (l₂ := [-78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1548)) (literal (valuationOf q) (1556)) (literal (valuationOf q) (1561)) (countLit q [-72, -75, -77]) (countLit q [-78, -80, -83, -85]) (count1559 q) 1 2 (meaning1548 q) (meaning1556 q) (meaning1561 q) hs
  change valuationOf q 1548 = false ∨ valuationOf q 1556 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1548 = false ∨ valuation q 1556 = false ∨ valuation q 1561 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1549 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1561 = true := by
  have hs : count1559 q = (countLit q [-72, -75, -77]) + (countLit q [-78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -75, -77]) (l₂ := [-78, -80, -83, -85])
  have hm := merge_two (literal (valuationOf q) (1549)) (literal (valuationOf q) (1555)) (literal (valuationOf q) (1561)) (countLit q [-72, -75, -77]) (countLit q [-78, -80, -83, -85]) (count1559 q) 2 1 (meaning1549 q) (meaning1555 q) (meaning1561 q) hs
  change valuationOf q 1549 = false ∨ valuationOf q 1555 = false ∨ valuationOf q 1561 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1549 = false ∨ valuation q 1555 = false ∨ valuation q 1561 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1559 = false ∨ valuationOf q 1566 = true := by
  have hs : count1566 q = (countLit q [-57, -59, -63, -65, -67, -69, -70]) + (countLit q [-72, -75, -77, -78, -80, -83, -85]) := List.countP_append (p := literal q) (l₁ := [-57, -59, -63, -65, -67, -69, -70]) (l₂ := [-72, -75, -77, -78, -80, -83, -85])
  have hm := merge_right (literal (valuationOf q) (1559)) (literal (valuationOf q) (1566)) (countLit q [-57, -59, -63, -65, -67, -69, -70]) (countLit q [-72, -75, -77, -78, -80, -83, -85]) (count1566 q) 1 (meaning1559 q) (meaning1566 q) hs
  change valuationOf q 1559 = false ∨ valuationOf q 1566 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1559 = false ∨ valuation q 1566 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E169.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112169
