import E112256Semantics
import B112E256Inputs
namespace Snake9.Regrowth.E112256
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_right (literal (valuationOf q) (1021)) (literal (valuationOf q) (1025)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 2 (meaning1021 q) (meaning1025 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1025 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1022 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_right (literal (valuationOf q) (1022)) (literal (valuationOf q) (1026)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 3 (meaning1022 q) (meaning1026 q) hs
  change valuationOf q 1022 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1022 = false ∨ valuation q 1026 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_right (literal (valuationOf q) (1023)) (literal (valuationOf q) (1027)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 4 (meaning1023 q) (meaning1027 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1027 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_left (literal (valuationOf q) (1012)) (literal (valuationOf q) (1024)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 1 (meaning1012 q) (meaning1024 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1024 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1025)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 1 1 (meaning1012 q) (meaning1020 q) (meaning1025 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1020 = false ∨ valuation q 1025 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1026)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 1 2 (meaning1012 q) (meaning1021 q) (meaning1026 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1021 = false ∨ valuation q 1026 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1027)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 1 3 (meaning1012 q) (meaning1022 q) (meaning1027 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1022 = false ∨ valuation q 1027 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1028)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 1 4 (meaning1012 q) (meaning1023 q) (meaning1028 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1023 = false ∨ valuation q 1028 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_left (literal (valuationOf q) (1013)) (literal (valuationOf q) (1025)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 2 (meaning1013 q) (meaning1025 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1025 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1026)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 2 1 (meaning1013 q) (meaning1020 q) (meaning1026 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1020 = false ∨ valuation q 1026 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1027)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 2 2 (meaning1013 q) (meaning1021 q) (meaning1027 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1021 = false ∨ valuation q 1027 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1028)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 2 3 (meaning1013 q) (meaning1022 q) (meaning1028 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1022 = false ∨ valuation q 1028 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1029)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 2 4 (meaning1013 q) (meaning1023 q) (meaning1029 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1023 = false ∨ valuation q 1029 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_left (literal (valuationOf q) (1014)) (literal (valuationOf q) (1026)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 3 (meaning1014 q) (meaning1026 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1026 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1027)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 3 1 (meaning1014 q) (meaning1020 q) (meaning1027 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1020 = false ∨ valuation q 1027 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1028)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 3 2 (meaning1014 q) (meaning1021 q) (meaning1028 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1021 = false ∨ valuation q 1028 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1029)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 3 3 (meaning1014 q) (meaning1022 q) (meaning1029 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1022 = false ∨ valuation q 1029 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_left (literal (valuationOf q) (1015)) (literal (valuationOf q) (1027)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 4 (meaning1015 q) (meaning1027 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1027 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1015)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1028)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 4 1 (meaning1015 q) (meaning1020 q) (meaning1028 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1020 = false ∨ valuation q 1028 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1015 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-76, -78, -79, -83]) + (countLit q [-84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-76, -78, -79, -83]) (l₂ := [-84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1015)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1029)) (countLit q [-76, -78, -79, -83]) (countLit q [-84, -88, -90, -91]) (count1024 q) 4 2 (meaning1015 q) (meaning1021 q) (meaning1029 q) hs
  change valuationOf q 1015 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1015 = false ∨ valuation q 1021 = false ∨ valuation q 1029 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1025 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_right (literal (valuationOf q) (1025)) (literal (valuationOf q) (1033)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 2 (meaning1025 q) (meaning1033 q) hs
  change valuationOf q 1025 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1025 = false ∨ valuation q 1033 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1026 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_right (literal (valuationOf q) (1026)) (literal (valuationOf q) (1034)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 3 (meaning1026 q) (meaning1034 q) hs
  change valuationOf q 1026 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1026 = false ∨ valuation q 1034 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1027 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_right (literal (valuationOf q) (1027)) (literal (valuationOf q) (1035)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 4 (meaning1027 q) (meaning1035 q) hs
  change valuationOf q 1027 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1027 = false ∨ valuation q 1035 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1028 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_right (literal (valuationOf q) (1028)) (literal (valuationOf q) (1036)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 5 (meaning1028 q) (meaning1036 q) hs
  change valuationOf q 1028 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1028 = false ∨ valuation q 1036 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1029 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_right (literal (valuationOf q) (1029)) (literal (valuationOf q) (1037)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 6 (meaning1029 q) (meaning1037 q) hs
  change valuationOf q 1029 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1029 = false ∨ valuation q 1037 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1033)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 1 1 (meaning1001 q) (meaning1024 q) (meaning1033 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1033 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1024 = false ∨ valuation q 1033 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1025)) (literal (valuationOf q) (1034)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 1 2 (meaning1001 q) (meaning1025 q) (meaning1034 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1025 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1025 = false ∨ valuation q 1034 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1035 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1026)) (literal (valuationOf q) (1035)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 1 3 (meaning1001 q) (meaning1026 q) (meaning1035 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1026 = false ∨ valuationOf q 1035 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1026 = false ∨ valuation q 1035 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1036 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1027)) (literal (valuationOf q) (1036)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 1 4 (meaning1001 q) (meaning1027 q) (meaning1036 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1027 = false ∨ valuationOf q 1036 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1027 = false ∨ valuation q 1036 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1028)) (literal (valuationOf q) (1037)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 1 5 (meaning1001 q) (meaning1028 q) (meaning1037 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1028 = false ∨ valuationOf q 1037 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1028 = false ∨ valuation q 1037 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1001 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1001)) (literal (valuationOf q) (1029)) (literal (valuationOf q) (1038)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 1 6 (meaning1001 q) (meaning1029 q) (meaning1038 q) hs
  change valuationOf q 1001 = false ∨ valuationOf q 1029 = false ∨ valuationOf q 1038 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1001 = false ∨ valuation q 1029 = false ∨ valuation q 1038 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true := by
  have hs : count1032 q = (countLit q [-62, -63, -65, -67, -68, -70, -74]) + (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) := List.countP_append (p := literal q) (l₁ := [-62, -63, -65, -67, -68, -70, -74]) (l₂ := [-76, -78, -79, -83, -84, -88, -90, -91])
  have hm := merge_two (literal (valuationOf q) (1002)) (literal (valuationOf q) (1024)) (literal (valuationOf q) (1034)) (countLit q [-62, -63, -65, -67, -68, -70, -74]) (countLit q [-76, -78, -79, -83, -84, -88, -90, -91]) (count1032 q) 2 1 (meaning1002 q) (meaning1024 q) (meaning1034 q) hs
  change valuationOf q 1002 = false ∨ valuationOf q 1024 = false ∨ valuationOf q 1034 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1002 = false ∨ valuation q 1024 = false ∨ valuation q 1034 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E256.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112256
