import E112088Semantics
import B112E088Inputs
namespace Snake9.Regrowth.E112088
noncomputable section
local instance blockDec19 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause609 (q : Nat → Bool) : valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true := by
  have hs : count339 q = (countLit q [160, 161, 162, 163, 164, 165, 166]) + (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [160, 161, 162, 163, 164, 165, 166]) (l₂ := [167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (323)) (literal (valuationOf q) (337)) (literal (valuationOf q) (340)) (countLit q [160, 161, 162, 163, 164, 165, 166]) (countLit q [167, 168, 169, 170, 171, 172, 173, 174]) (count339 q) 1 1 (meaning323 q) (meaning337 q) (meaning340 q) hs
  change valuationOf q 323 = false ∨ valuationOf q 337 = false ∨ valuationOf q 340 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause609 (q : Snake 81) (h : Conditions q) : valuation q 323 = false ∨ valuation q 337 = false ∨ valuation q 340 = true := counterClause609 (baseVal q)

theorem counterClause610 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause610 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause610 (baseVal q)

theorem counterClause611 (q : Nat → Bool) : valuationOf q 340 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (340)) (literal (valuationOf q) (342)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 2 (meaning340 q) (meaning342 q) hs
  change valuationOf q 340 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause611 (q : Snake 81) (h : Conditions q) : valuation q 340 = false ∨ valuation q 342 = true := counterClause611 (baseVal q)

theorem counterClause612 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (311)) (literal (valuationOf q) (341)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 (meaning311 q) (meaning341 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause612 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 341 = true := counterClause612 (baseVal q)

theorem counterClause613 (q : Nat → Bool) : valuationOf q 311 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (311)) (literal (valuationOf q) (339)) (literal (valuationOf q) (342)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 1 1 (meaning311 q) (meaning339 q) (meaning342 q) hs
  change valuationOf q 311 = false ∨ valuationOf q 339 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause613 (q : Snake 81) (h : Conditions q) : valuation q 311 = false ∨ valuation q 339 = false ∨ valuation q 342 = true := counterClause613 (baseVal q)

theorem counterClause614 (q : Nat → Bool) : valuationOf q 312 = false ∨ valuationOf q 342 = true := by
  have hs : count341 q = (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) + (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (l₂ := [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (312)) (literal (valuationOf q) (342)) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]) (countLit q [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count341 q) 2 (meaning312 q) (meaning342 q) hs
  change valuationOf q 312 = false ∨ valuationOf q 342 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause614 (q : Snake 81) (h : Conditions q) : valuation q 312 = false ∨ valuation q 342 = true := counterClause614 (baseVal q)

theorem counterClause615 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause615 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause615 (baseVal q)

theorem counterClause616 (q : Nat → Bool) : valuationOf q 342 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_right (literal (valuationOf q) (342)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning342 q) (meaning344 q) hs
  change valuationOf q 342 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause616 (q : Snake 81) (h : Conditions q) : valuation q 342 = false ∨ valuation q 344 = true := counterClause616 (baseVal q)

theorem counterClause617 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (285)) (literal (valuationOf q) (343)) (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 (meaning285 q) (meaning343 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause617 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 343 = true := counterClause617 (baseVal q)

theorem counterClause618 (q : Nat → Bool) : valuationOf q 285 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_two (literal (valuationOf q) (285)) (literal (valuationOf q) (341)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 1 1 (meaning285 q) (meaning341 q) (meaning344 q) hs
  change valuationOf q 285 = false ∨ valuationOf q 341 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause618 (q : Snake 81) (h : Conditions q) : valuation q 285 = false ∨ valuation q 341 = false ∨ valuation q 344 = true := counterClause618 (baseVal q)

theorem counterClause619 (q : Nat → Bool) : valuationOf q 286 = false ∨ valuationOf q 344 = true := by
  have hs : count343 q = (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) + (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) := List.countP_append (p := literal q) (l₁ := [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (l₂ := [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174])
  have hm := merge_left (literal (valuationOf q) (286)) (literal (valuationOf q) (344)) (countLit q [117, 118, 119, 120, 121, 122, 123, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145]) (countLit q [146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174]) (count343 q) 2 (meaning286 q) (meaning344 q) hs
  change valuationOf q 286 = false ∨ valuationOf q 344 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause619 (q : Snake 81) (h : Conditions q) : valuation q 286 = false ∨ valuation q 344 = true := counterClause619 (baseVal q)

theorem counterClause620 (q : Nat → Bool) : valuationOf q 176 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [176]) + (countLit q [177]) := List.countP_append (p := literal q) (l₁ := [176]) (l₂ := [177])
  have hm := merge_left (literal (valuationOf q) (176)) (literal (valuationOf q) (345)) (countLit q [176]) (countLit q [177]) (count345 q) 1 (meaning176 q) (meaning345 q) hs
  change valuationOf q 176 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause620 (q : Snake 81) (h : Conditions q) : valuation q 176 = false ∨ valuation q 345 = true := counterClause620 (baseVal q)

theorem counterClause621 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [175]) + (countLit q [176, 177]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176, 177])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [175]) (countLit q [176, 177]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause621 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause621 (baseVal q)

theorem counterClause622 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [178]) + (countLit q [179]) := List.countP_append (p := literal q) (l₁ := [178]) (l₂ := [179])
  have hm := merge_left (literal (valuationOf q) (178)) (literal (valuationOf q) (349)) (countLit q [178]) (countLit q [179]) (count349 q) 1 (meaning178 q) (meaning349 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause622 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 349 = true := counterClause622 (baseVal q)

theorem counterClause623 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [178, 179]) + (countLit q [180, 181]) := List.countP_append (p := literal q) (l₁ := [178, 179]) (l₂ := [180, 181])
  have hm := merge_left (literal (valuationOf q) (349)) (literal (valuationOf q) (353)) (countLit q [178, 179]) (countLit q [180, 181]) (count353 q) 1 (meaning349 q) (meaning353 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause623 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 353 = true := counterClause623 (baseVal q)

theorem counterClause624 (q : Nat → Bool) : valuationOf q 353 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [175, 176, 177]) + (countLit q [178, 179, 180, 181]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177]) (l₂ := [178, 179, 180, 181])
  have hm := merge_right (literal (valuationOf q) (353)) (literal (valuationOf q) (355)) (countLit q [175, 176, 177]) (countLit q [178, 179, 180, 181]) (count355 q) 1 (meaning353 q) (meaning355 q) hs
  change valuationOf q 353 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause624 (q : Snake 81) (h : Conditions q) : valuation q 353 = false ∨ valuation q 355 = true := counterClause624 (baseVal q)

theorem counterClause625 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [175, 176, 177]) + (countLit q [178, 179, 180, 181]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177]) (l₂ := [178, 179, 180, 181])
  have hm := merge_left (literal (valuationOf q) (347)) (literal (valuationOf q) (355)) (countLit q [175, 176, 177]) (countLit q [178, 179, 180, 181]) (count355 q) 1 (meaning347 q) (meaning355 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause625 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 355 = true := counterClause625 (baseVal q)

theorem counterClause626 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_right (literal (valuationOf q) (184)) (literal (valuationOf q) (357)) (countLit q [183]) (countLit q [184]) (count357 q) 1 (meaning184 q) (meaning357 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause626 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 357 = true := counterClause626 (baseVal q)

theorem counterClause627 (q : Nat → Bool) : valuationOf q 183 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [183]) + (countLit q [184]) := List.countP_append (p := literal q) (l₁ := [183]) (l₂ := [184])
  have hm := merge_left (literal (valuationOf q) (183)) (literal (valuationOf q) (357)) (countLit q [183]) (countLit q [184]) (count357 q) 1 (meaning183 q) (meaning357 q) hs
  change valuationOf q 183 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause627 (q : Snake 81) (h : Conditions q) : valuation q 183 = false ∨ valuation q 357 = true := counterClause627 (baseVal q)

theorem counterClause628 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [182]) + (countLit q [183, 184]) := List.countP_append (p := literal q) (l₁ := [182]) (l₂ := [183, 184])
  have hm := merge_right (literal (valuationOf q) (357)) (literal (valuationOf q) (359)) (countLit q [182]) (countLit q [183, 184]) (count359 q) 1 (meaning357 q) (meaning359 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause628 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 359 = true := counterClause628 (baseVal q)

theorem counterClause629 (q : Nat → Bool) : valuationOf q 186 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_right (literal (valuationOf q) (186)) (literal (valuationOf q) (361)) (countLit q [185]) (countLit q [186]) (count361 q) 1 (meaning186 q) (meaning361 q) hs
  change valuationOf q 186 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause629 (q : Snake 81) (h : Conditions q) : valuation q 186 = false ∨ valuation q 361 = true := counterClause629 (baseVal q)

theorem counterClause630 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (363)) (countLit q [187]) (countLit q [188]) (count363 q) 1 (meaning188 q) (meaning363 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause630 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 363 = true := counterClause630 (baseVal q)

theorem counterClause631 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [185, 186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [185, 186]) (l₂ := [187, 188])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [185, 186]) (countLit q [187, 188]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause631 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause631 (baseVal q)

theorem counterClause632 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [185, 186]) + (countLit q [187, 188]) := List.countP_append (p := literal q) (l₁ := [185, 186]) (l₂ := [187, 188])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (365)) (countLit q [185, 186]) (countLit q [187, 188]) (count365 q) 1 (meaning361 q) (meaning365 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause632 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 365 = true := counterClause632 (baseVal q)

theorem counterClause633 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [182, 183, 184]) + (countLit q [185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [182, 183, 184]) (l₂ := [185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (365)) (literal (valuationOf q) (367)) (countLit q [182, 183, 184]) (countLit q [185, 186, 187, 188]) (count367 q) 1 (meaning365 q) (meaning367 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause633 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 367 = true := counterClause633 (baseVal q)

theorem counterClause634 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [182, 183, 184]) + (countLit q [185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [182, 183, 184]) (l₂ := [185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (359)) (literal (valuationOf q) (367)) (countLit q [182, 183, 184]) (countLit q [185, 186, 187, 188]) (count367 q) 1 (meaning359 q) (meaning367 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause634 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 367 = true := counterClause634 (baseVal q)

theorem counterClause635 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_right (literal (valuationOf q) (367)) (literal (valuationOf q) (369)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 (meaning367 q) (meaning369 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause635 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 369 = true := counterClause635 (baseVal q)

theorem counterClause636 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (369)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 (meaning355 q) (meaning369 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause636 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 369 = true := counterClause636 (baseVal q)

theorem counterClause637 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true := by
  have hs : count369 q = (countLit q [175, 176, 177, 178, 179, 180, 181]) + (countLit q [182, 183, 184, 185, 186, 187, 188]) := List.countP_append (p := literal q) (l₁ := [175, 176, 177, 178, 179, 180, 181]) (l₂ := [182, 183, 184, 185, 186, 187, 188])
  have hm := merge_two (literal (valuationOf q) (355)) (literal (valuationOf q) (367)) (literal (valuationOf q) (370)) (countLit q [175, 176, 177, 178, 179, 180, 181]) (countLit q [182, 183, 184, 185, 186, 187, 188]) (count369 q) 1 1 (meaning355 q) (meaning367 q) (meaning370 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 367 = false ∨ valuationOf q 370 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause637 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 367 = false ∨ valuation q 370 = true := counterClause637 (baseVal q)

theorem counterClause638 (q : Nat → Bool) : valuationOf q 200 = false ∨ valuationOf q 389 = true := by
  have hs : count389 q = (countLit q [200]) + (countLit q [201]) := List.countP_append (p := literal q) (l₁ := [200]) (l₂ := [201])
  have hm := merge_left (literal (valuationOf q) (200)) (literal (valuationOf q) (389)) (countLit q [200]) (countLit q [201]) (count389 q) 1 (meaning200 q) (meaning389 q) hs
  change valuationOf q 200 = false ∨ valuationOf q 389 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause638 (q : Snake 81) (h : Conditions q) : valuation q 200 = false ∨ valuation q 389 = true := counterClause638 (baseVal q)

theorem counterClause639 (q : Nat → Bool) : valuationOf q 389 = false ∨ valuationOf q 393 = true := by
  have hs : count393 q = (countLit q [200, 201]) + (countLit q [202, 203]) := List.countP_append (p := literal q) (l₁ := [200, 201]) (l₂ := [202, 203])
  have hm := merge_left (literal (valuationOf q) (389)) (literal (valuationOf q) (393)) (countLit q [200, 201]) (countLit q [202, 203]) (count393 q) 1 (meaning389 q) (meaning393 q) hs
  change valuationOf q 389 = false ∨ valuationOf q 393 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause639 (q : Snake 81) (h : Conditions q) : valuation q 389 = false ∨ valuation q 393 = true := counterClause639 (baseVal q)

theorem counterClause640 (q : Nat → Bool) : valuationOf q 393 = false ∨ valuationOf q 395 = true := by
  have hs : count395 q = (countLit q [196, 197, 198, 199]) + (countLit q [200, 201, 202, 203]) := List.countP_append (p := literal q) (l₁ := [196, 197, 198, 199]) (l₂ := [200, 201, 202, 203])
  have hm := merge_right (literal (valuationOf q) (393)) (literal (valuationOf q) (395)) (countLit q [196, 197, 198, 199]) (countLit q [200, 201, 202, 203]) (count395 q) 1 (meaning393 q) (meaning395 q) hs
  change valuationOf q 393 = false ∨ valuationOf q 395 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause640 (q : Snake 81) (h : Conditions q) : valuation q 393 = false ∨ valuation q 395 = true := counterClause640 (baseVal q)

theorem block19 (q : Snake 81) (h : Conditions q) : B112E088.Block19 (valuation q) :=
  ⟨clause609 q h, clause610 q h, clause611 q h, clause612 q h, clause613 q h, clause614 q h, clause615 q h, clause616 q h, clause617 q h, clause618 q h, clause619 q h, clause620 q h, clause621 q h, clause622 q h, clause623 q h, clause624 q h, clause625 q h, clause626 q h, clause627 q h, clause628 q h, clause629 q h, clause630 q h, clause631 q h, clause632 q h, clause633 q h, clause634 q h, clause635 q h, clause636 q h, clause637 q h, clause638 q h, clause639 q h, clause640 q h⟩

end
end Snake9.Regrowth.E112088
