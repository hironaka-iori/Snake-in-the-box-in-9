import E112260Semantics
import B112E260Inputs
namespace Snake9.Regrowth.E112260
noncomputable section
local instance blockDec47 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause1505 (q : Nat → Bool) : valuationOf q 1011 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_right (literal (valuationOf q) (1011)) (literal (valuationOf q) (1013)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1012 q) 2 (meaning1011 q) (meaning1013 q) hs
  change valuationOf q 1011 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1505 (q : Snake 81) (h : Conditions q) : valuation q 1011 = false ∨ valuation q 1013 = true := counterClause1505 (baseVal q)

theorem counterClause1506 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1012 = true := by
  have hs : count1012 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_left (literal (valuationOf q) (1008)) (literal (valuationOf q) (1012)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1012 q) 1 (meaning1008 q) (meaning1012 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1012 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1506 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1012 = true := counterClause1506 (baseVal q)

theorem counterClause1507 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1013)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1012 q) 1 1 (meaning1008 q) (meaning1010 q) (meaning1013 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1507 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1010 = false ∨ valuation q 1013 = true := counterClause1507 (baseVal q)

theorem counterClause1508 (q : Nat → Bool) : valuationOf q 1008 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1014 = true := by
  have hs : count1012 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (1008)) (literal (valuationOf q) (1011)) (literal (valuationOf q) (1014)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1012 q) 1 2 (meaning1008 q) (meaning1011 q) (meaning1014 q) hs
  change valuationOf q 1008 = false ∨ valuationOf q 1011 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1508 (q : Snake 81) (h : Conditions q) : valuation q 1008 = false ∨ valuation q 1011 = false ∨ valuation q 1014 = true := counterClause1508 (baseVal q)

theorem counterClause1509 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1013 = true := by
  have hs : count1012 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_left (literal (valuationOf q) (1009)) (literal (valuationOf q) (1013)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1012 q) 2 (meaning1009 q) (meaning1013 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1013 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1509 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1013 = true := counterClause1509 (baseVal q)

theorem counterClause1510 (q : Nat → Bool) : valuationOf q 1009 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1014 = true := by
  have hs : count1012 q = (countLit q [-76, -79]) + (countLit q [-81, -82]) := List.countP_append (p := literal q) (l₁ := [-76, -79]) (l₂ := [-81, -82])
  have hm := merge_two (literal (valuationOf q) (1009)) (literal (valuationOf q) (1010)) (literal (valuationOf q) (1014)) (countLit q [-76, -79]) (countLit q [-81, -82]) (count1012 q) 2 1 (meaning1009 q) (meaning1010 q) (meaning1014 q) hs
  change valuationOf q 1009 = false ∨ valuationOf q 1010 = false ∨ valuationOf q 1014 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1510 (q : Snake 81) (h : Conditions q) : valuation q 1009 = false ∨ valuation q 1010 = false ∨ valuation q 1014 = true := counterClause1510 (baseVal q)

theorem counterClause1511 (q : Nat → Bool) : valuationOf q 86 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_right (literal (valuationOf q) (-86)) (literal (valuationOf q) (1016)) (countLit q [-85]) (countLit q [-86]) (count1016 q) 1 (meaningNeg86 q) (meaning1016 q) hs
  change (! (valuationOf q 86)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1511 (q : Snake 81) (h : Conditions q) : valuation q 86 = true ∨ valuation q 1016 = true := counterClause1511 (baseVal q)

theorem counterClause1512 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1016 = true := by
  have hs : count1016 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1016)) (countLit q [-85]) (countLit q [-86]) (count1016 q) 1 (meaningNeg85 q) (meaning1016 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1016 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1512 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1016 = true := counterClause1512 (baseVal q)

theorem counterClause1513 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 86 = true ∨ valuationOf q 1017 = true := by
  have hs : count1016 q = (countLit q [-85]) + (countLit q [-86]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-86])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-86)) (literal (valuationOf q) (1017)) (countLit q [-85]) (countLit q [-86]) (count1016 q) 1 1 (meaningNeg85 q) (meaningNeg86 q) (meaning1017 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 86)) = false ∨ valuationOf q 1017 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1513 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 86 = true ∨ valuation q 1017 = true := counterClause1513 (baseVal q)

theorem counterClause1514 (q : Nat → Bool) : valuationOf q 90 = true ∨ valuationOf q 1018 = true := by
  have hs : count1018 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_right (literal (valuationOf q) (-90)) (literal (valuationOf q) (1018)) (countLit q [-89]) (countLit q [-90]) (count1018 q) 1 (meaningNeg90 q) (meaning1018 q) hs
  change (! (valuationOf q 90)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1514 (q : Snake 81) (h : Conditions q) : valuation q 90 = true ∨ valuation q 1018 = true := counterClause1514 (baseVal q)

theorem counterClause1515 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1018 = true := by
  have hs : count1018 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1018)) (countLit q [-89]) (countLit q [-90]) (count1018 q) 1 (meaningNeg89 q) (meaning1018 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1018 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1515 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1018 = true := counterClause1515 (baseVal q)

theorem counterClause1516 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 90 = true ∨ valuationOf q 1019 = true := by
  have hs : count1018 q = (countLit q [-89]) + (countLit q [-90]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-90])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-90)) (literal (valuationOf q) (1019)) (countLit q [-89]) (countLit q [-90]) (count1018 q) 1 1 (meaningNeg89 q) (meaningNeg90 q) (meaning1019 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 90)) = false ∨ valuationOf q 1019 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause1516 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 90 = true ∨ valuation q 1019 = true := counterClause1516 (baseVal q)

theorem counterClause1517 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1020 = true := by
  have hs : count1020 q = (countLit q [-85, -86]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-85, -86]) (l₂ := [-89, -90])
  have hm := merge_left (literal (valuationOf q) (1016)) (literal (valuationOf q) (1020)) (countLit q [-85, -86]) (countLit q [-89, -90]) (count1020 q) 1 (meaning1016 q) (meaning1020 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1020 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1517 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1020 = true := counterClause1517 (baseVal q)

theorem counterClause1518 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-85, -86]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-85, -86]) (l₂ := [-89, -90])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1021)) (countLit q [-85, -86]) (countLit q [-89, -90]) (count1020 q) 1 1 (meaning1016 q) (meaning1018 q) (meaning1021 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1518 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1018 = false ∨ valuation q 1021 = true := counterClause1518 (baseVal q)

theorem counterClause1519 (q : Nat → Bool) : valuationOf q 1016 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1022 = true := by
  have hs : count1020 q = (countLit q [-85, -86]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-85, -86]) (l₂ := [-89, -90])
  have hm := merge_two (literal (valuationOf q) (1016)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1022)) (countLit q [-85, -86]) (countLit q [-89, -90]) (count1020 q) 1 2 (meaning1016 q) (meaning1019 q) (meaning1022 q) hs
  change valuationOf q 1016 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1519 (q : Snake 81) (h : Conditions q) : valuation q 1016 = false ∨ valuation q 1019 = false ∨ valuation q 1022 = true := counterClause1519 (baseVal q)

theorem counterClause1520 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1021 = true := by
  have hs : count1020 q = (countLit q [-85, -86]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-85, -86]) (l₂ := [-89, -90])
  have hm := merge_left (literal (valuationOf q) (1017)) (literal (valuationOf q) (1021)) (countLit q [-85, -86]) (countLit q [-89, -90]) (count1020 q) 2 (meaning1017 q) (meaning1021 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1021 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1520 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1021 = true := counterClause1520 (baseVal q)

theorem counterClause1521 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1022 = true := by
  have hs : count1020 q = (countLit q [-85, -86]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-85, -86]) (l₂ := [-89, -90])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1018)) (literal (valuationOf q) (1022)) (countLit q [-85, -86]) (countLit q [-89, -90]) (count1020 q) 2 1 (meaning1017 q) (meaning1018 q) (meaning1022 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1018 = false ∨ valuationOf q 1022 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1521 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1018 = false ∨ valuation q 1022 = true := counterClause1521 (baseVal q)

theorem counterClause1522 (q : Nat → Bool) : valuationOf q 1017 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1023 = true := by
  have hs : count1020 q = (countLit q [-85, -86]) + (countLit q [-89, -90]) := List.countP_append (p := literal q) (l₁ := [-85, -86]) (l₂ := [-89, -90])
  have hm := merge_two (literal (valuationOf q) (1017)) (literal (valuationOf q) (1019)) (literal (valuationOf q) (1023)) (countLit q [-85, -86]) (countLit q [-89, -90]) (count1020 q) 2 2 (meaning1017 q) (meaning1019 q) (meaning1023 q) hs
  change valuationOf q 1017 = false ∨ valuationOf q 1019 = false ∨ valuationOf q 1023 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1522 (q : Snake 81) (h : Conditions q) : valuation q 1017 = false ∨ valuation q 1019 = false ∨ valuation q 1023 = true := counterClause1522 (baseVal q)

theorem counterClause1523 (q : Nat → Bool) : valuationOf q 1020 = false ∨ valuationOf q 1024 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1020)) (literal (valuationOf q) (1024)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 1 (meaning1020 q) (meaning1024 q) hs
  change valuationOf q 1020 = false ∨ valuationOf q 1024 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1523 (q : Snake 81) (h : Conditions q) : valuation q 1020 = false ∨ valuation q 1024 = true := counterClause1523 (baseVal q)

theorem counterClause1524 (q : Nat → Bool) : valuationOf q 1021 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1021)) (literal (valuationOf q) (1025)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 2 (meaning1021 q) (meaning1025 q) hs
  change valuationOf q 1021 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1524 (q : Snake 81) (h : Conditions q) : valuation q 1021 = false ∨ valuation q 1025 = true := counterClause1524 (baseVal q)

theorem counterClause1525 (q : Nat → Bool) : valuationOf q 1022 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1022)) (literal (valuationOf q) (1026)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 3 (meaning1022 q) (meaning1026 q) hs
  change valuationOf q 1022 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1525 (q : Snake 81) (h : Conditions q) : valuation q 1022 = false ∨ valuation q 1026 = true := counterClause1525 (baseVal q)

theorem counterClause1526 (q : Nat → Bool) : valuationOf q 1023 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_right (literal (valuationOf q) (1023)) (literal (valuationOf q) (1027)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 4 (meaning1023 q) (meaning1027 q) hs
  change valuationOf q 1023 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1526 (q : Snake 81) (h : Conditions q) : valuation q 1023 = false ∨ valuation q 1027 = true := counterClause1526 (baseVal q)

theorem counterClause1527 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1025)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 1 1 (meaning1012 q) (meaning1020 q) (meaning1025 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1527 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1020 = false ∨ valuation q 1025 = true := counterClause1527 (baseVal q)

theorem counterClause1528 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1026)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 1 2 (meaning1012 q) (meaning1021 q) (meaning1026 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1528 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1021 = false ∨ valuation q 1026 = true := counterClause1528 (baseVal q)

theorem counterClause1529 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1027)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 1 3 (meaning1012 q) (meaning1022 q) (meaning1027 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1529 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1022 = false ∨ valuation q 1027 = true := counterClause1529 (baseVal q)

theorem counterClause1530 (q : Nat → Bool) : valuationOf q 1012 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1012)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1028)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 1 4 (meaning1012 q) (meaning1023 q) (meaning1028 q) hs
  change valuationOf q 1012 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1530 (q : Snake 81) (h : Conditions q) : valuation q 1012 = false ∨ valuation q 1023 = false ∨ valuation q 1028 = true := counterClause1530 (baseVal q)

theorem counterClause1531 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1025 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_left (literal (valuationOf q) (1013)) (literal (valuationOf q) (1025)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 2 (meaning1013 q) (meaning1025 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1025 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1531 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1025 = true := counterClause1531 (baseVal q)

theorem counterClause1532 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1026 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1026)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 2 1 (meaning1013 q) (meaning1020 q) (meaning1026 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1026 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1532 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1020 = false ∨ valuation q 1026 = true := counterClause1532 (baseVal q)

theorem counterClause1533 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1021)) (literal (valuationOf q) (1027)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 2 2 (meaning1013 q) (meaning1021 q) (meaning1027 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1021 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1533 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1021 = false ∨ valuation q 1027 = true := counterClause1533 (baseVal q)

theorem counterClause1534 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1028 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1022)) (literal (valuationOf q) (1028)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 2 3 (meaning1013 q) (meaning1022 q) (meaning1028 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1022 = false ∨ valuationOf q 1028 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1534 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1022 = false ∨ valuation q 1028 = true := counterClause1534 (baseVal q)

theorem counterClause1535 (q : Nat → Bool) : valuationOf q 1013 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1029 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1013)) (literal (valuationOf q) (1023)) (literal (valuationOf q) (1029)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 2 4 (meaning1013 q) (meaning1023 q) (meaning1029 q) hs
  change valuationOf q 1013 = false ∨ valuationOf q 1023 = false ∨ valuationOf q 1029 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1535 (q : Snake 81) (h : Conditions q) : valuation q 1013 = false ∨ valuation q 1023 = false ∨ valuation q 1029 = true := counterClause1535 (baseVal q)

theorem counterClause1536 (q : Nat → Bool) : valuationOf q 1014 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1027 = true := by
  have hs : count1024 q = (countLit q [-76, -79, -81, -82]) + (countLit q [-85, -86, -89, -90]) := List.countP_append (p := literal q) (l₁ := [-76, -79, -81, -82]) (l₂ := [-85, -86, -89, -90])
  have hm := merge_two (literal (valuationOf q) (1014)) (literal (valuationOf q) (1020)) (literal (valuationOf q) (1027)) (countLit q [-76, -79, -81, -82]) (countLit q [-85, -86, -89, -90]) (count1024 q) 3 1 (meaning1014 q) (meaning1020 q) (meaning1027 q) hs
  change valuationOf q 1014 = false ∨ valuationOf q 1020 = false ∨ valuationOf q 1027 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause1536 (q : Snake 81) (h : Conditions q) : valuation q 1014 = false ∨ valuation q 1020 = false ∨ valuation q 1027 = true := counterClause1536 (baseVal q)

theorem block47 (q : Snake 81) (h : Conditions q) : B112E260.Block47 (valuation q) :=
  ⟨clause1505 q h, clause1506 q h, clause1507 q h, clause1508 q h, clause1509 q h, clause1510 q h, clause1511 q h, clause1512 q h, clause1513 q h, clause1514 q h, clause1515 q h, clause1516 q h, clause1517 q h, clause1518 q h, clause1519 q h, clause1520 q h, clause1521 q h, clause1522 q h, clause1523 q h, clause1524 q h, clause1525 q h, clause1526 q h, clause1527 q h, clause1528 q h, clause1529 q h, clause1530 q h, clause1531 q h, clause1532 q h, clause1533 q h, clause1534 q h, clause1535 q h, clause1536 q h⟩

end
end Snake9.Regrowth.E112260
