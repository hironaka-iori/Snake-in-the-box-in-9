import E112091Semantics
import B112E091Inputs
namespace Snake9.Regrowth.E112091
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 1412 = false ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81, -83])
  have hm := merge_right (literal (valuationOf q) (1412)) (literal (valuationOf q) (1414)) (countLit q [-78]) (countLit q [-81, -83]) (count1414 q) 1 (meaning1412 q) (meaning1414 q) hs
  change valuationOf q 1412 = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 1412 = false ∨ valuation q 1414 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1414 = true := by
  have hs : count1414 q = (countLit q [-78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81, -83])
  have hm := merge_left (literal (valuationOf q) (-78)) (literal (valuationOf q) (1414)) (countLit q [-78]) (countLit q [-81, -83]) (count1414 q) 1 (meaningNeg78 q) (meaning1414 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1414 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1414 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 78 = true ∨ valuationOf q 1412 = false ∨ valuationOf q 1415 = true := by
  have hs : count1414 q = (countLit q [-78]) + (countLit q [-81, -83]) := List.countP_append (p := literal q) (l₁ := [-78]) (l₂ := [-81, -83])
  have hm := merge_two (literal (valuationOf q) (-78)) (literal (valuationOf q) (1412)) (literal (valuationOf q) (1415)) (countLit q [-78]) (countLit q [-81, -83]) (count1414 q) 1 1 (meaningNeg78 q) (meaning1412 q) (meaning1415 q) hs
  change (! (valuationOf q 78)) = false ∨ valuationOf q 1412 = false ∨ valuationOf q 1415 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 78 = true ∨ valuation q 1412 = false ∨ valuation q 1415 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 87 = true ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_right (literal (valuationOf q) (-87)) (literal (valuationOf q) (1417)) (countLit q [-85]) (countLit q [-87]) (count1417 q) 1 (meaningNeg87 q) (meaning1417 q) hs
  change (! (valuationOf q 87)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 87 = true ∨ valuation q 1417 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 1417 = true := by
  have hs : count1417 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_left (literal (valuationOf q) (-85)) (literal (valuationOf q) (1417)) (countLit q [-85]) (countLit q [-87]) (count1417 q) 1 (meaningNeg85 q) (meaning1417 q) hs
  change (! (valuationOf q 85)) = false ∨ valuationOf q 1417 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 1417 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 85 = true ∨ valuationOf q 87 = true ∨ valuationOf q 1418 = true := by
  have hs : count1417 q = (countLit q [-85]) + (countLit q [-87]) := List.countP_append (p := literal q) (l₁ := [-85]) (l₂ := [-87])
  have hm := merge_two (literal (valuationOf q) (-85)) (literal (valuationOf q) (-87)) (literal (valuationOf q) (1418)) (countLit q [-85]) (countLit q [-87]) (count1417 q) 1 1 (meaningNeg85 q) (meaningNeg87 q) (meaning1418 q) hs
  change (! (valuationOf q 85)) = false ∨ (! (valuationOf q 87)) = false ∨ valuationOf q 1418 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 85 = true ∨ valuation q 87 = true ∨ valuation q 1418 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 91 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_right (literal (valuationOf q) (-91)) (literal (valuationOf q) (1419)) (countLit q [-89]) (countLit q [-91]) (count1419 q) 1 (meaningNeg91 q) (meaning1419 q) hs
  change (! (valuationOf q 91)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 91 = true ∨ valuation q 1419 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 1419 = true := by
  have hs : count1419 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_left (literal (valuationOf q) (-89)) (literal (valuationOf q) (1419)) (countLit q [-89]) (countLit q [-91]) (count1419 q) 1 (meaningNeg89 q) (meaning1419 q) hs
  change (! (valuationOf q 89)) = false ∨ valuationOf q 1419 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 1419 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 89 = true ∨ valuationOf q 91 = true ∨ valuationOf q 1420 = true := by
  have hs : count1419 q = (countLit q [-89]) + (countLit q [-91]) := List.countP_append (p := literal q) (l₁ := [-89]) (l₂ := [-91])
  have hm := merge_two (literal (valuationOf q) (-89)) (literal (valuationOf q) (-91)) (literal (valuationOf q) (1420)) (countLit q [-89]) (countLit q [-91]) (count1419 q) 1 1 (meaningNeg89 q) (meaningNeg91 q) (meaning1420 q) hs
  change (! (valuationOf q 89)) = false ∨ (! (valuationOf q 91)) = false ∨ valuationOf q 1420 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 89 = true ∨ valuation q 91 = true ∨ valuation q 1420 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 1419 = false ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_right (literal (valuationOf q) (1419)) (literal (valuationOf q) (1421)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1421 q) 1 (meaning1419 q) (meaning1421 q) hs
  change valuationOf q 1419 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 1419 = false ∨ valuation q 1421 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 1420 = false ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_right (literal (valuationOf q) (1420)) (literal (valuationOf q) (1422)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1421 q) 2 (meaning1420 q) (meaning1422 q) hs
  change valuationOf q 1420 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 1420 = false ∨ valuation q 1422 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1421 = true := by
  have hs : count1421 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_left (literal (valuationOf q) (1417)) (literal (valuationOf q) (1421)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1421 q) 1 (meaning1417 q) (meaning1421 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1421 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1421 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1422)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1421 q) 1 1 (meaning1417 q) (meaning1419 q) (meaning1422 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1419 = false ∨ valuation q 1422 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 1417 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true := by
  have hs : count1421 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1417)) (literal (valuationOf q) (1420)) (literal (valuationOf q) (1423)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1421 q) 1 2 (meaning1417 q) (meaning1420 q) (meaning1423 q) hs
  change valuationOf q 1417 = false ∨ valuationOf q 1420 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 1417 = false ∨ valuation q 1420 = false ∨ valuation q 1423 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1422 = true := by
  have hs : count1421 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_left (literal (valuationOf q) (1418)) (literal (valuationOf q) (1422)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1421 q) 2 (meaning1418 q) (meaning1422 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1422 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1422 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 1418 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1423 = true := by
  have hs : count1421 q = (countLit q [-85, -87]) + (countLit q [-89, -91]) := List.countP_append (p := literal q) (l₁ := [-85, -87]) (l₂ := [-89, -91])
  have hm := merge_two (literal (valuationOf q) (1418)) (literal (valuationOf q) (1419)) (literal (valuationOf q) (1423)) (countLit q [-85, -87]) (countLit q [-89, -91]) (count1421 q) 2 1 (meaning1418 q) (meaning1419 q) (meaning1423 q) hs
  change valuationOf q 1418 = false ∨ valuationOf q 1419 = false ∨ valuationOf q 1423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 1418 = false ∨ valuation q 1419 = false ∨ valuation q 1423 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 1421 = false ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-78, -81, -83]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1421)) (literal (valuationOf q) (1425)) (countLit q [-78, -81, -83]) (countLit q [-85, -87, -89, -91]) (count1425 q) 1 (meaning1421 q) (meaning1425 q) hs
  change valuationOf q 1421 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 1421 = false ∨ valuation q 1425 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 1422 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-78, -81, -83]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1422)) (literal (valuationOf q) (1426)) (countLit q [-78, -81, -83]) (countLit q [-85, -87, -89, -91]) (count1425 q) 2 (meaning1422 q) (meaning1426 q) hs
  change valuationOf q 1422 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 1422 = false ∨ valuation q 1426 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 1423 = false ∨ valuationOf q 1427 = true := by
  have hs : count1425 q = (countLit q [-78, -81, -83]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_right (literal (valuationOf q) (1423)) (literal (valuationOf q) (1427)) (countLit q [-78, -81, -83]) (countLit q [-85, -87, -89, -91]) (count1425 q) 3 (meaning1423 q) (meaning1427 q) hs
  change valuationOf q 1423 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 1423 = false ∨ valuation q 1427 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1425 = true := by
  have hs : count1425 q = (countLit q [-78, -81, -83]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1414)) (literal (valuationOf q) (1425)) (countLit q [-78, -81, -83]) (countLit q [-85, -87, -89, -91]) (count1425 q) 1 (meaning1414 q) (meaning1425 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1425 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1425 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-78, -81, -83]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1426)) (countLit q [-78, -81, -83]) (countLit q [-85, -87, -89, -91]) (count1425 q) 1 1 (meaning1414 q) (meaning1421 q) (meaning1426 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1421 = false ∨ valuation q 1426 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true := by
  have hs : count1425 q = (countLit q [-78, -81, -83]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1422)) (literal (valuationOf q) (1427)) (countLit q [-78, -81, -83]) (countLit q [-85, -87, -89, -91]) (count1425 q) 1 2 (meaning1414 q) (meaning1422 q) (meaning1427 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1422 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1422 = false ∨ valuation q 1427 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 1414 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true := by
  have hs : count1425 q = (countLit q [-78, -81, -83]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1414)) (literal (valuationOf q) (1423)) (literal (valuationOf q) (1428)) (countLit q [-78, -81, -83]) (countLit q [-85, -87, -89, -91]) (count1425 q) 1 3 (meaning1414 q) (meaning1423 q) (meaning1428 q) hs
  change valuationOf q 1414 = false ∨ valuationOf q 1423 = false ∨ valuationOf q 1428 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 1414 = false ∨ valuation q 1423 = false ∨ valuation q 1428 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1426 = true := by
  have hs : count1425 q = (countLit q [-78, -81, -83]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_left (literal (valuationOf q) (1415)) (literal (valuationOf q) (1426)) (countLit q [-78, -81, -83]) (countLit q [-85, -87, -89, -91]) (count1425 q) 2 (meaning1415 q) (meaning1426 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1426 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1426 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 1415 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1427 = true := by
  have hs : count1425 q = (countLit q [-78, -81, -83]) + (countLit q [-85, -87, -89, -91]) := List.countP_append (p := literal q) (l₁ := [-78, -81, -83]) (l₂ := [-85, -87, -89, -91])
  have hm := merge_two (literal (valuationOf q) (1415)) (literal (valuationOf q) (1421)) (literal (valuationOf q) (1427)) (countLit q [-78, -81, -83]) (countLit q [-85, -87, -89, -91]) (count1425 q) 2 1 (meaning1415 q) (meaning1421 q) (meaning1427 q) hs
  change valuationOf q 1415 = false ∨ valuationOf q 1421 = false ∨ valuationOf q 1427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 1415 = false ∨ valuation q 1421 = false ∨ valuation q 1427 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 98 = true ∨ valuationOf q 1432 = true := by
  have hs : count1432 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_right (literal (valuationOf q) (-98)) (literal (valuationOf q) (1432)) (countLit q [-96]) (countLit q [-98]) (count1432 q) 1 (meaningNeg98 q) (meaning1432 q) hs
  change (! (valuationOf q 98)) = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 98 = true ∨ valuation q 1432 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 1432 = true := by
  have hs : count1432 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_left (literal (valuationOf q) (-96)) (literal (valuationOf q) (1432)) (countLit q [-96]) (countLit q [-98]) (count1432 q) 1 (meaningNeg96 q) (meaning1432 q) hs
  change (! (valuationOf q 96)) = false ∨ valuationOf q 1432 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 1432 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 96 = true ∨ valuationOf q 98 = true ∨ valuationOf q 1433 = true := by
  have hs : count1432 q = (countLit q [-96]) + (countLit q [-98]) := List.countP_append (p := literal q) (l₁ := [-96]) (l₂ := [-98])
  have hm := merge_two (literal (valuationOf q) (-96)) (literal (valuationOf q) (-98)) (literal (valuationOf q) (1433)) (countLit q [-96]) (countLit q [-98]) (count1432 q) 1 1 (meaningNeg96 q) (meaningNeg98 q) (meaning1433 q) hs
  change (! (valuationOf q 96)) = false ∨ (! (valuationOf q 98)) = false ∨ valuationOf q 1433 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 96 = true ∨ valuation q 98 = true ∨ valuation q 1433 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 1432 = false ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-93]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96, -98])
  have hm := merge_right (literal (valuationOf q) (1432)) (literal (valuationOf q) (1434)) (countLit q [-93]) (countLit q [-96, -98]) (count1434 q) 1 (meaning1432 q) (meaning1434 q) hs
  change valuationOf q 1432 = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 1432 = false ∨ valuation q 1434 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1434 = true := by
  have hs : count1434 q = (countLit q [-93]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96, -98])
  have hm := merge_left (literal (valuationOf q) (-93)) (literal (valuationOf q) (1434)) (countLit q [-93]) (countLit q [-96, -98]) (count1434 q) 1 (meaningNeg93 q) (meaning1434 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1434 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1434 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1432 = false ∨ valuationOf q 1435 = true := by
  have hs : count1434 q = (countLit q [-93]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96, -98])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (1432)) (literal (valuationOf q) (1435)) (countLit q [-93]) (countLit q [-96, -98]) (count1434 q) 1 1 (meaningNeg93 q) (meaning1432 q) (meaning1435 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1432 = false ∨ valuationOf q 1435 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1432 = false ∨ valuation q 1435 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 93 = true ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true := by
  have hs : count1434 q = (countLit q [-93]) + (countLit q [-96, -98]) := List.countP_append (p := literal q) (l₁ := [-93]) (l₂ := [-96, -98])
  have hm := merge_two (literal (valuationOf q) (-93)) (literal (valuationOf q) (1433)) (literal (valuationOf q) (1436)) (countLit q [-93]) (countLit q [-96, -98]) (count1434 q) 1 2 (meaningNeg93 q) (meaning1433 q) (meaning1436 q) hs
  change (! (valuationOf q 93)) = false ∨ valuationOf q 1433 = false ∨ valuationOf q 1436 = true at hm
  simpa only [Bool.not_eq_false'] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 93 = true ∨ valuation q 1433 = false ∨ valuation q 1436 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E091.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112091
