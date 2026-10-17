import E112168Semantics
import B112E168Inputs
namespace Snake9.Regrowth.E112168
noncomputable section
local instance blockDec30 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause961 (q : Nat → Bool) : valuationOf q 1517 = false ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-72]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1517)) (literal (valuationOf q) (1519)) (countLit q [-72]) (countLit q [-76, -77]) (count1519 q) 1 (meaning1517 q) (meaning1519 q) hs
  change valuationOf q 1517 = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause961 (q : Snake 81) (h : Conditions q) : valuation q 1517 = false ∨ valuation q 1519 = true := counterClause961 (baseVal q)

theorem counterClause962 (q : Nat → Bool) : valuationOf q 1518 = false ∨ valuationOf q 1520 = true := by
  have hs : count1519 q = (countLit q [-72]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76, -77])
  have hm := merge_right (literal (valuationOf q) (1518)) (literal (valuationOf q) (1520)) (countLit q [-72]) (countLit q [-76, -77]) (count1519 q) 2 (meaning1518 q) (meaning1520 q) hs
  change valuationOf q 1518 = false ∨ valuationOf q 1520 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause962 (q : Snake 81) (h : Conditions q) : valuation q 1518 = false ∨ valuation q 1520 = true := counterClause962 (baseVal q)

theorem counterClause963 (q : Nat → Bool) : valuationOf q 72 = true ∨ valuationOf q 1519 = true := by
  have hs : count1519 q = (countLit q [-72]) + (countLit q [-76, -77]) := List.countP_append (p := literal q) (l₁ := [-72]) (l₂ := [-76, -77])
  have hm := merge_left (literal (valuationOf q) (-72)) (literal (valuationOf q) (1519)) (countLit q [-72]) (countLit q [-76, -77]) (count1519 q) 1 (meaningNeg72 q) (meaning1519 q) hs
  change (! (valuationOf q 72)) = false ∨ valuationOf q 1519 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause963 (q : Snake 81) (h : Conditions q) : valuation q 72 = true ∨ valuation q 1519 = true := counterClause963 (baseVal q)

theorem counterClause964 (q : Nat → Bool) : valuationOf q 82 = true ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_right (literal (valuationOf q) (-82)) (literal (valuationOf q) (1522)) (countLit q [-78]) (countLit q [-82]) (count1522 q) 1 (meaningNeg82 q) (meaning1522 q) hs
  change (! (valuationOf q 82)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause964 (q : Snake 81) (h : Conditions q) : valuation q 82 = true ∨ valuation q 1522 = true := counterClause964 (baseVal q)

theorem counterClause965 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1522 = true := by
  have hs : count1522 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1522)) (countLit q [-78]) (countLit q [-82]) (count1522 q) 1 (meaningNeg78 q) (meaning1522 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1522 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause965 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1522 = true := counterClause965 (baseVal q)

theorem counterClause966 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 82 = true ∨ valuationOf q 1523 = true := by
  have hs : count1522 q = (countLit q [-78]) + (countLit q [-82]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-82])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (-82)) (literal (valuationOf q) (1523)) (countLit q [-78]) (countLit q [-82]) (count1522 q) 1 1 (meaningNeg78 q) (meaningNeg82 q) (meaning1523 q) hs
  change (! (valuationOf q 78)) = false ∨ (! (valuationOf q 82)) = false ∨ valuationOf q 1523 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause966 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 82 = true ∨ valuation q 1523 = true := counterClause966 (baseVal q)

theorem counterClause967 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_right (literal (valuationOf q) (-85)) (literal (valuationOf q) (1524)) (countLit q [-84]) (countLit q [-85]) (count1524 q) 1 (meaningNeg85 q) (meaning1524 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause967 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1524 = true := counterClause967 (baseVal q)

theorem counterClause968 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 1524 = true := by
  have hs : count1524 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_left (literal (valuationOf q) (-84)) (literal (valuationOf q) (1524)) (countLit q [-84]) (countLit q [-85]) (count1524 q) 1 (meaningNeg84 q) (meaning1524 q) hs
  change (! (valuationOf q 84)) = false ∨ valuationOf q 1524 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause968 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 1524 = true := counterClause968 (baseVal q)

theorem counterClause969 (q : Nat → Bool) : valuationOf q 84 = true ∨ valuationOf q 85 = true ∨ valuationOf q 1525 = true := by
  have hs : count1524 q = (countLit q [-84]) + (countLit q [-85]) := List.countP_append (p := literal q) (l₁ := [-84]) (l₂ := [-85])
  have hm := merge_two (literal (valuationOf q) (-84)) (literal (valuationOf q) (-85)) (literal (valuationOf q) (1525)) (countLit q [-84]) (countLit q [-85]) (count1524 q) 1 1 (meaningNeg84 q) (meaningNeg85 q) (meaning1525 q) hs
  change (! (valuationOf q 84)) = false ∨ (! (valuationOf q 85)) = false ∨ valuationOf q 1525 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause969 (q : Snake 81) (h : Conditions q) : valuation q 84 = true ∨ valuation q 85 = true ∨ valuation q 1525 = true := counterClause969 (baseVal q)

theorem counterClause970 (q : Nat → Bool) : valuationOf q 1524 = false ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-78, -82]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -82]) (l₂ := [-84, -85])
  have hm := merge_right (literal (valuationOf q) (1524)) (literal (valuationOf q) (1526)) (countLit q [-78, -82]) (countLit q [-84, -85]) (count1526 q) 1 (meaning1524 q) (meaning1526 q) hs
  change valuationOf q 1524 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause970 (q : Snake 81) (h : Conditions q) : valuation q 1524 = false ∨ valuation q 1526 = true := counterClause970 (baseVal q)

theorem counterClause971 (q : Nat → Bool) : valuationOf q 1525 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-78, -82]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -82]) (l₂ := [-84, -85])
  have hm := merge_right (literal (valuationOf q) (1525)) (literal (valuationOf q) (1527)) (countLit q [-78, -82]) (countLit q [-84, -85]) (count1526 q) 2 (meaning1525 q) (meaning1527 q) hs
  change valuationOf q 1525 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause971 (q : Snake 81) (h : Conditions q) : valuation q 1525 = false ∨ valuation q 1527 = true := counterClause971 (baseVal q)

theorem counterClause972 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1526 = true := by
  have hs : count1526 q = (countLit q [-78, -82]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -82]) (l₂ := [-84, -85])
  have hm := merge_left (literal (valuationOf q) (1522)) (literal (valuationOf q) (1526)) (countLit q [-78, -82]) (countLit q [-84, -85]) (count1526 q) 1 (meaning1522 q) (meaning1526 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1526 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause972 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1526 = true := counterClause972 (baseVal q)

theorem counterClause973 (q : Nat → Bool) : valuationOf q 1522 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-78, -82]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -82]) (l₂ := [-84, -85])
  have hm := merge_two (literal (valuationOf q) (1522)) (literal (valuationOf q) (1524)) (literal (valuationOf q) (1527)) (countLit q [-78, -82]) (countLit q [-84, -85]) (count1526 q) 1 1 (meaning1522 q) (meaning1524 q) (meaning1527 q) hs
  change valuationOf q 1522 = false ∨ valuationOf q 1524 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause973 (q : Snake 81) (h : Conditions q) : valuation q 1522 = false ∨ valuation q 1524 = false ∨ valuation q 1527 = true := counterClause973 (baseVal q)

theorem counterClause974 (q : Nat → Bool) : valuationOf q 1523 = false ∨ valuationOf q 1527 = true := by
  have hs : count1526 q = (countLit q [-78, -82]) + (countLit q [-84, -85]) := List.countP_append (p := literal q) (l₁ := [-78, -82]) (l₂ := [-84, -85])
  have hm := merge_left (literal (valuationOf q) (1523)) (literal (valuationOf q) (1527)) (countLit q [-78, -82]) (countLit q [-84, -85]) (count1526 q) 2 (meaning1523 q) (meaning1527 q) hs
  change valuationOf q 1523 = false ∨ valuationOf q 1527 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause974 (q : Snake 81) (h : Conditions q) : valuation q 1523 = false ∨ valuation q 1527 = true := counterClause974 (baseVal q)

theorem counterClause975 (q : Nat → Bool) : valuationOf q 1526 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -82, -84, -85])
  have hm := merge_right (literal (valuationOf q) (1526)) (literal (valuationOf q) (1530)) (countLit q [-72, -76, -77]) (countLit q [-78, -82, -84, -85]) (count1530 q) 1 (meaning1526 q) (meaning1530 q) hs
  change valuationOf q 1526 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause975 (q : Snake 81) (h : Conditions q) : valuation q 1526 = false ∨ valuation q 1530 = true := counterClause975 (baseVal q)

theorem counterClause976 (q : Nat → Bool) : valuationOf q 1527 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -82, -84, -85])
  have hm := merge_right (literal (valuationOf q) (1527)) (literal (valuationOf q) (1531)) (countLit q [-72, -76, -77]) (countLit q [-78, -82, -84, -85]) (count1530 q) 2 (meaning1527 q) (meaning1531 q) hs
  change valuationOf q 1527 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause976 (q : Snake 81) (h : Conditions q) : valuation q 1527 = false ∨ valuation q 1531 = true := counterClause976 (baseVal q)

theorem counterClause977 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1530 = true := by
  have hs : count1530 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -82, -84, -85])
  have hm := merge_left (literal (valuationOf q) (1519)) (literal (valuationOf q) (1530)) (countLit q [-72, -76, -77]) (countLit q [-78, -82, -84, -85]) (count1530 q) 1 (meaning1519 q) (meaning1530 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1530 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause977 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1530 = true := counterClause977 (baseVal q)

theorem counterClause978 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1531)) (countLit q [-72, -76, -77]) (countLit q [-78, -82, -84, -85]) (count1530 q) 1 1 (meaning1519 q) (meaning1526 q) (meaning1531 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause978 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1526 = false ∨ valuation q 1531 = true := counterClause978 (baseVal q)

theorem counterClause979 (q : Nat → Bool) : valuationOf q 1519 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1519)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1532)) (countLit q [-72, -76, -77]) (countLit q [-78, -82, -84, -85]) (count1530 q) 1 2 (meaning1519 q) (meaning1527 q) (meaning1532 q) hs
  change valuationOf q 1519 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause979 (q : Snake 81) (h : Conditions q) : valuation q 1519 = false ∨ valuation q 1527 = false ∨ valuation q 1532 = true := counterClause979 (baseVal q)

theorem counterClause980 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1531 = true := by
  have hs : count1530 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -82, -84, -85])
  have hm := merge_left (literal (valuationOf q) (1520)) (literal (valuationOf q) (1531)) (countLit q [-72, -76, -77]) (countLit q [-78, -82, -84, -85]) (count1530 q) 2 (meaning1520 q) (meaning1531 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1531 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause980 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1531 = true := counterClause980 (baseVal q)

theorem counterClause981 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1532 = true := by
  have hs : count1530 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1526)) (literal (valuationOf q) (1532)) (countLit q [-72, -76, -77]) (countLit q [-78, -82, -84, -85]) (count1530 q) 2 1 (meaning1520 q) (meaning1526 q) (meaning1532 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1526 = false ∨ valuationOf q 1532 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause981 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1526 = false ∨ valuation q 1532 = true := counterClause981 (baseVal q)

theorem counterClause982 (q : Nat → Bool) : valuationOf q 1520 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1533 = true := by
  have hs : count1530 q = (countLit q [-72, -76, -77]) + (countLit q [-78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-72, -76, -77]) (l₂ := [-78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1520)) (literal (valuationOf q) (1527)) (literal (valuationOf q) (1533)) (countLit q [-72, -76, -77]) (countLit q [-78, -82, -84, -85]) (count1530 q) 2 2 (meaning1520 q) (meaning1527 q) (meaning1533 q) hs
  change valuationOf q 1520 = false ∨ valuationOf q 1527 = false ∨ valuationOf q 1533 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause982 (q : Snake 81) (h : Conditions q) : valuation q 1520 = false ∨ valuation q 1527 = false ∨ valuation q 1533 = true := counterClause982 (baseVal q)

theorem counterClause983 (q : Nat → Bool) : valuationOf q 1531 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_right (literal (valuationOf q) (1531)) (literal (valuationOf q) (1538)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 2 (meaning1531 q) (meaning1538 q) hs
  change valuationOf q 1531 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause983 (q : Snake 81) (h : Conditions q) : valuation q 1531 = false ∨ valuation q 1538 = true := counterClause983 (baseVal q)

theorem counterClause984 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1537 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_left (literal (valuationOf q) (1510)) (literal (valuationOf q) (1537)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 1 (meaning1510 q) (meaning1537 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1537 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause984 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1537 = true := counterClause984 (baseVal q)

theorem counterClause985 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1538)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 1 1 (meaning1510 q) (meaning1530 q) (meaning1538 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause985 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1530 = false ∨ valuation q 1538 = true := counterClause985 (baseVal q)

theorem counterClause986 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1539)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 1 2 (meaning1510 q) (meaning1531 q) (meaning1539 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause986 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1531 = false ∨ valuation q 1539 = true := counterClause986 (baseVal q)

theorem counterClause987 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1540)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 1 3 (meaning1510 q) (meaning1532 q) (meaning1540 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause987 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1532 = false ∨ valuation q 1540 = true := counterClause987 (baseVal q)

theorem counterClause988 (q : Nat → Bool) : valuationOf q 1510 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1510)) (literal (valuationOf q) (1533)) (literal (valuationOf q) (1541)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 1 4 (meaning1510 q) (meaning1533 q) (meaning1541 q) hs
  change valuationOf q 1510 = false ∨ valuationOf q 1533 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause988 (q : Snake 81) (h : Conditions q) : valuation q 1510 = false ∨ valuation q 1533 = false ∨ valuation q 1541 = true := counterClause988 (baseVal q)

theorem counterClause989 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1538 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_left (literal (valuationOf q) (1511)) (literal (valuationOf q) (1538)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 2 (meaning1511 q) (meaning1538 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1538 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause989 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1538 = true := counterClause989 (baseVal q)

theorem counterClause990 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1539 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1530)) (literal (valuationOf q) (1539)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 2 1 (meaning1511 q) (meaning1530 q) (meaning1539 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1530 = false ∨ valuationOf q 1539 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause990 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1530 = false ∨ valuation q 1539 = true := counterClause990 (baseVal q)

theorem counterClause991 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1540 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1531)) (literal (valuationOf q) (1540)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 2 2 (meaning1511 q) (meaning1531 q) (meaning1540 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1531 = false ∨ valuationOf q 1540 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause991 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1531 = false ∨ valuation q 1540 = true := counterClause991 (baseVal q)

theorem counterClause992 (q : Nat → Bool) : valuationOf q 1511 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1541 = true := by
  have hs : count1537 q = (countLit q [-60, -61, -62, -66, -68, -69, -70]) + (countLit q [-72, -76, -77, -78, -82, -84, -85]) := List.countP_append (p := literal q) (l₁ := [-60, -61, -62, -66, -68, -69, -70]) (l₂ := [-72, -76, -77, -78, -82, -84, -85])
  have hm := merge_two (literal (valuationOf q) (1511)) (literal (valuationOf q) (1532)) (literal (valuationOf q) (1541)) (countLit q [-60, -61, -62, -66, -68, -69, -70]) (countLit q [-72, -76, -77, -78, -82, -84, -85]) (count1537 q) 2 3 (meaning1511 q) (meaning1532 q) (meaning1541 q) hs
  change valuationOf q 1511 = false ∨ valuationOf q 1532 = false ∨ valuationOf q 1541 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause992 (q : Snake 81) (h : Conditions q) : valuation q 1511 = false ∨ valuation q 1532 = false ∨ valuation q 1541 = true := counterClause992 (baseVal q)

theorem block30 (q : Snake 81) (h : Conditions q) : B112E168.Block30 (valuation q) :=
  ⟨clause961 q h, clause962 q h, clause963 q h, clause964 q h, clause965 q h, clause966 q h, clause967 q h, clause968 q h, clause969 q h, clause970 q h, clause971 q h, clause972 q h, clause973 q h, clause974 q h, clause975 q h, clause976 q h, clause977 q h, clause978 q h, clause979 q h, clause980 q h, clause981 q h, clause982 q h, clause983 q h, clause984 q h, clause985 q h, clause986 q h, clause987 q h, clause988 q h, clause989 q h, clause990 q h, clause991 q h, clause992 q h⟩

end
end Snake9.Regrowth.E112168
