import E112169Semantics
import B112E169Inputs
namespace Snake9.Regrowth.E112169
noncomputable section
local instance blockDec18 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause577 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (337)) (literal (valuationOf q) (339)) (countLit q [160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 1 (meaning337 q) (meaning339 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause577 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 339 = true := counterClause577 (baseVal q)

theorem counterClause578 (q : Nat → Bool) : valuationOf q 338 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (338)) (literal (valuationOf q) (340)) (countLit q [160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 2 (meaning338 q) (meaning340 q) hs
  change valuationOf q 338 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause578 (q : Snake 81) (h : Conditions q) : valuation q 338 = false ∨ valuation q 340 = true := counterClause578 (baseVal q)

theorem counterClause579 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (323)) (literal (valuationOf q) (339)) (countLit q [160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 1 (meaning323 q) (meaning339 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause579 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 339 = true := counterClause579 (baseVal q)

theorem counterClause580 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 1 1 (meaning323 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause580 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause580 (baseVal q)

theorem counterClause581 (q : Nat → Bool) : valuationOf q 324 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (324)) (literal (valuationOf q) (340)) (countLit q [160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 2 (meaning324 q) (meaning340 q) hs
  change valuationOf q 324 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause581 (q : Snake 81) (h : Conditions q) : valuation q 324 = false ∨ valuation q 340 = true := counterClause581 (baseVal q)

theorem counterClause582 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause582 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause582 (baseVal q)

theorem counterClause583 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (340)) (literal (valuationOf q) (342)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 2 (meaning340 q) (meaning342 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause583 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 342 = true := counterClause583 (baseVal q)

theorem counterClause584 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (341)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 (meaning311 q) (meaning341 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause584 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 341 = true := counterClause584 (baseVal q)

theorem counterClause585 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (311)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 1 (meaning311 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause585 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause585 (baseVal q)

theorem counterClause586 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (312)) (literal (valuationOf q) (342)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 2 (meaning312 q) (meaning342 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause586 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 342 = true := counterClause586 (baseVal q)

theorem counterClause587 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause587 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause587 (baseVal q)

theorem counterClause588 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (342)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning342 q) (meaning344 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause588 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 344 = true := counterClause588 (baseVal q)

theorem counterClause589 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (343)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning285 q) (meaning343 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause589 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 343 = true := counterClause589 (baseVal q)

theorem counterClause590 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (285)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 1 (meaning285 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause590 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause590 (baseVal q)

theorem counterClause591 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (286)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 124, 125, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning286 q) (meaning344 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause591 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 344 = true := counterClause591 (baseVal q)

theorem counterClause592 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176, 177])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (347)) (countLit q [175]) (countLit q [176, 177]) (count347 q) 1 (meaning175 q) (meaning347 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause592 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 347 = true := counterClause592 (baseVal q)

theorem counterClause593 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [178]) + (countLit q [179]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179])
  have hm := merge_right (literal (valuationOf q) (179)) (literal (valuationOf q) (349)) (countLit q [178]) (countLit q [179]) (count349 q) 1 (meaning179 q) (meaning349 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause593 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 349 = true := counterClause593 (baseVal q)

theorem counterClause594 (q : Nat → Bool) : valuationOf q 181 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_right (literal (valuationOf q) (181)) (literal (valuationOf q) (351)) (countLit q [180]) (countLit q [181]) (count351 q) 1 (meaning181 q) (meaning351 q) hs
  change valuationOf q 181 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause594 (q : Snake 81) (h : Conditions q) : valuation q 181 = false ∨ valuation q 351 = true := counterClause594 (baseVal q)

theorem counterClause595 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [178, 179]) + (countLit q [180, 181]) := List.countP_append (p := literal q) (l₁ := [178, 179]) (l₂ := [180, 181])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [178, 179]) (countLit q [180, 181]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause595 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause595 (baseVal q)

theorem counterClause596 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [178, 179]) + (countLit q [180, 181]) := List.countP_append (p := literal q) (l₁ := [178, 179]) (l₂ := [180, 181])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (353)) (countLit q [178, 179]) (countLit q [180, 181]) (count353 q) 1 (meaning349 q) (meaning353 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause596 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 353 = true := counterClause596 (baseVal q)

theorem counterClause597 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [175, 176, 177]) + (countLit q [178, 179, 180, 181]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177]) (l₂ := [178, 179, 180, 181])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [175, 176, 177]) (countLit q [178, 179, 180, 181]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause597 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause597 (baseVal q)

theorem counterClause598 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [175, 176, 177]) + (countLit q [178, 179, 180, 181]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177]) (l₂ := [178, 179, 180, 181])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (355)) (countLit q [175, 176, 177]) (countLit q [178, 179, 180, 181]) (count355 q) 1 (meaning347 q) (meaning355 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause598 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 355 = true := counterClause598 (baseVal q)

theorem counterClause599 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (357)) (countLit q [183]) (countLit q [184]) (count357 q) 1 (meaning183 q) (meaning357 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause599 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 357 = true := counterClause599 (baseVal q)

theorem counterClause600 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183, 184])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [182]) (countLit q [183, 184]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause600 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause600 (baseVal q)

theorem counterClause601 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_right (literal (valuationOf q) (186)) (literal (valuationOf q) (361)) (countLit q [185]) (countLit q [186]) (count361 q) 1 (meaning186 q) (meaning361 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause601 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 361 = true := counterClause601 (baseVal q)

theorem counterClause602 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [185, 186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [185, 186]) (l₂ := [187, 188])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (365)) (countLit q [185, 186]) (countLit q [187, 188]) (count365 q) 1 (meaning361 q) (meaning365 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause602 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 365 = true := counterClause602 (baseVal q)

theorem counterClause603 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [182, 183, 184]) + (countLit q [185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [182, 183, 184]) (l₂ := [185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [182, 183, 184]) (countLit q [185, 186, 187, 188]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause603 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause603 (baseVal q)

theorem counterClause604 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [182, 183, 184]) + (countLit q [185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [182, 183, 184]) (l₂ := [185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (367)) (countLit q [182, 183, 184]) (countLit q [185, 186, 187, 188]) (count367 q) 1 (meaning359 q) (meaning367 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause604 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 367 = true := counterClause604 (baseVal q)

theorem counterClause605 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause605 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause605 (baseVal q)

theorem counterClause606 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (369)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 (meaning355 q) (meaning369 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause606 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 369 = true := counterClause606 (baseVal q)

theorem counterClause607 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_two (literal (valuationOf q) (355)) (literal (valuationOf q) (367)) (literal (valuationOf q) (370)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 1 (meaning355 q) (meaning367 q) (meaning370 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause607 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 367 = false ∨ valuation q 370 = true := counterClause607 (baseVal q)

theorem counterClause608 (q : Nat → Bool) : valuationOf q 193 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [192]) + (countLit q [193]) := List.countP_append (p := literal q) (l₁ := [192]) (l₂ := [193])
  have hm := merge_right (literal (valuationOf q) (193)) (literal (valuationOf q) (375)) (countLit q [192]) (countLit q [193]) (count375 q) 1 (meaning193 q) (meaning375 q) hs
  change valuationOf q 193 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause608 (q : Snake 81) (h : Conditions q) : valuation q 193 = false ∨ valuation q 375 = true := counterClause608 (baseVal q)

theorem block18 (q : Snake 81) (h : Conditions q) : B112E169.Block18 (valuation q) :=
  ⟨clause577 q h, clause578 q h, clause579 q h, clause580 q h, clause581 q h, clause582 q h, clause583 q h, clause584 q h, clause585 q h, clause586 q h, clause587 q h, clause588 q h, clause589 q h, clause590 q h, clause591 q h, clause592 q h, clause593 q h, clause594 q h, clause595 q h, clause596 q h, clause597 q h, clause598 q h, clause599 q h, clause600 q h, clause601 q h, clause602 q h, clause603 q h, clause604 q h, clause605 q h, clause606 q h, clause607 q h, clause608 q h⟩

end
end Snake9.Regrowth.E112169
