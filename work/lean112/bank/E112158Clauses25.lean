import E112158Semantics
import B112E158Inputs
namespace Snake9.Regrowth.E112158
noncomputable section
local instance blockDec25 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause801 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true := by
  have hs : count329 q = (countLit q [162, 163, 164]) + (countLit q [165, 166, 167, 168]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164]) (l₂ := [165, 166, 167, 168])
  have hm := merge_two (literal (valuationOf q) (321)) (literal (valuationOf q) (327)) (literal (valuationOf q) (330)) (countLit q [162, 163, 164]) (countLit q [165, 166, 167, 168]) (count329 q) 1 1 (meaning321 q) (meaning327 q) (meaning330 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 327 = false ∨ valuationOf q 330 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause801 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 327 = false ∨ valuation q 330 = true := counterClause801 (baseVal q)

theorem counterClause802 (q : Nat → Bool) : valuationOf q 174 = false ∨ valuationOf q 337 = true := by
  have hs : count337 q = (countLit q [173]) + (countLit q [174]) := List.countP_append (p := literal q) (l₁ := [173]) (l₂ := [174])
  have hm := merge_right (literal (valuationOf q) (174)) (literal (valuationOf q) (337)) (countLit q [173]) (countLit q [174]) (count337 q) 1 (meaning174 q) (meaning337 q) hs
  change valuationOf q 174 = false ∨ valuationOf q 337 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause802 (q : Snake 81) (h : Conditions q) : valuation q 174 = false ∨ valuation q 337 = true := counterClause802 (baseVal q)

theorem counterClause803 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 339 = true := by
  have hs : count339 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (339)) (countLit q [175]) (countLit q [176]) (count339 q) 1 (meaning175 q) (meaning339 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 339 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause803 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 339 = true := counterClause803 (baseVal q)

theorem counterClause804 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_right (literal (valuationOf q) (339)) (literal (valuationOf q) (341)) (countLit q [173, 174]) (countLit q [175, 176]) (count341 q) 1 (meaning339 q) (meaning341 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause804 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 341 = true := counterClause804 (baseVal q)

theorem counterClause805 (q : Nat → Bool) : valuationOf q 337 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [173, 174]) + (countLit q [175, 176]) := List.countP_append (p := literal q) (l₁ := [173, 174]) (l₂ := [175, 176])
  have hm := merge_left (literal (valuationOf q) (337)) (literal (valuationOf q) (341)) (countLit q [173, 174]) (countLit q [175, 176]) (count341 q) 1 (meaning337 q) (meaning341 q) hs
  change valuationOf q 337 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause805 (q : Snake 81) (h : Conditions q) : valuation q 337 = false ∨ valuation q 341 = true := counterClause805 (baseVal q)

theorem counterClause806 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [169, 170, 171, 172]) + (countLit q [173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [169, 170, 171, 172]) (l₂ := [173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (countLit q [169, 170, 171, 172]) (countLit q [173, 174, 175, 176]) (count343 q) 1 (meaning341 q) (meaning343 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause806 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = true := counterClause806 (baseVal q)

theorem counterClause807 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause807 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause807 (baseVal q)

theorem counterClause808 (q : Nat → Bool) : valuationOf q 329 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (329)) (literal (valuationOf q) (345)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 1 (meaning329 q) (meaning345 q) hs
  change valuationOf q 329 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause808 (q : Snake 81) (h : Conditions q) : valuation q 329 = false ∨ valuation q 345 = true := counterClause808 (baseVal q)

theorem counterClause809 (q : Nat → Bool) : valuationOf q 330 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [162, 163, 164, 165, 166, 167, 168]) + (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [162, 163, 164, 165, 166, 167, 168]) (l₂ := [169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (330)) (literal (valuationOf q) (346)) (countLit q [162, 163, 164, 165, 166, 167, 168]) (countLit q [169, 170, 171, 172, 173, 174, 175, 176]) (count345 q) 2 (meaning330 q) (meaning346 q) hs
  change valuationOf q 330 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause809 (q : Snake 81) (h : Conditions q) : valuation q 330 = false ∨ valuation q 346 = true := counterClause809 (baseVal q)

theorem counterClause810 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause810 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause810 (baseVal q)

theorem counterClause811 (q : Nat → Bool) : valuationOf q 346 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (346)) (literal (valuationOf q) (348)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count347 q) 2 (meaning346 q) (meaning348 q) hs
  change valuationOf q 346 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause811 (q : Snake 81) (h : Conditions q) : valuation q 346 = false ∨ valuation q 348 = true := counterClause811 (baseVal q)

theorem counterClause812 (q : Nat → Bool) : valuationOf q 317 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) + (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (l₂ := [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (317)) (literal (valuationOf q) (347)) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161]) (countLit q [162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count347 q) 1 (meaning317 q) (meaning347 q) hs
  change valuationOf q 317 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause812 (q : Snake 81) (h : Conditions q) : valuation q 317 = false ∨ valuation q 347 = true := counterClause812 (baseVal q)

theorem counterClause813 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause813 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause813 (baseVal q)

theorem counterClause814 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_right (literal (valuationOf q) (348)) (literal (valuationOf q) (350)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 2 (meaning348 q) (meaning350 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause814 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 350 = true := counterClause814 (baseVal q)

theorem counterClause815 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (291)) (literal (valuationOf q) (349)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 1 (meaning291 q) (meaning349 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause815 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 349 = true := counterClause815 (baseVal q)

theorem counterClause816 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_two (literal (valuationOf q) (291)) (literal (valuationOf q) (347)) (literal (valuationOf q) (350)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 1 1 (meaning291 q) (meaning347 q) (meaning350 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause816 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 347 = false ∨ valuation q 350 = true := counterClause816 (baseVal q)

theorem counterClause817 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176])
  have hm := merge_left (literal (valuationOf q) (292)) (literal (valuationOf q) (350)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176]) (count349 q) 2 (meaning292 q) (meaning350 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause817 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 350 = true := counterClause817 (baseVal q)

theorem counterClause818 (q : Nat → Bool) : valuationOf q 180 = false ∨ valuationOf q 355 = true := by
  have hs : count355 q = (countLit q [180]) + (countLit q [181]) := List.countP_append (p := literal q) (l₁ := [180]) (l₂ := [181])
  have hm := merge_left (literal (valuationOf q) (180)) (literal (valuationOf q) (355)) (countLit q [180]) (countLit q [181]) (count355 q) 1 (meaning180 q) (meaning355 q) hs
  change valuationOf q 180 = false ∨ valuationOf q 355 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause818 (q : Snake 81) (h : Conditions q) : valuation q 180 = false ∨ valuation q 355 = true := counterClause818 (baseVal q)

theorem counterClause819 (q : Nat → Bool) : valuationOf q 355 = false ∨ valuationOf q 359 = true := by
  have hs : count359 q = (countLit q [180, 181]) + (countLit q [182, 183]) := List.countP_append (p := literal q) (l₁ := [180, 181]) (l₂ := [182, 183])
  have hm := merge_left (literal (valuationOf q) (355)) (literal (valuationOf q) (359)) (countLit q [180, 181]) (countLit q [182, 183]) (count359 q) 1 (meaning355 q) (meaning359 q) hs
  change valuationOf q 355 = false ∨ valuationOf q 359 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause819 (q : Snake 81) (h : Conditions q) : valuation q 355 = false ∨ valuation q 359 = true := counterClause819 (baseVal q)

theorem counterClause820 (q : Nat → Bool) : valuationOf q 359 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [177, 178, 179]) + (countLit q [180, 181, 182, 183]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179]) (l₂ := [180, 181, 182, 183])
  have hm := merge_right (literal (valuationOf q) (359)) (literal (valuationOf q) (361)) (countLit q [177, 178, 179]) (countLit q [180, 181, 182, 183]) (count361 q) 1 (meaning359 q) (meaning361 q) hs
  change valuationOf q 359 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause820 (q : Snake 81) (h : Conditions q) : valuation q 359 = false ∨ valuation q 361 = true := counterClause820 (baseVal q)

theorem counterClause821 (q : Nat → Bool) : valuationOf q 185 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [185]) + (countLit q [186]) := List.countP_append (p := literal q) (l₁ := [185]) (l₂ := [186])
  have hm := merge_left (literal (valuationOf q) (185)) (literal (valuationOf q) (363)) (countLit q [185]) (countLit q [186]) (count363 q) 1 (meaning185 q) (meaning363 q) hs
  change valuationOf q 185 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause821 (q : Snake 81) (h : Conditions q) : valuation q 185 = false ∨ valuation q 363 = true := counterClause821 (baseVal q)

theorem counterClause822 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185, 186])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [184]) (countLit q [185, 186]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause822 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause822 (baseVal q)

theorem counterClause823 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [184]) + (countLit q [185, 186]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185, 186])
  have hm := merge_left (literal (valuationOf q) (184)) (literal (valuationOf q) (365)) (countLit q [184]) (countLit q [185, 186]) (count365 q) 1 (meaning184 q) (meaning365 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause823 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 365 = true := counterClause823 (baseVal q)

theorem counterClause824 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (367)) (countLit q [187]) (countLit q [188]) (count367 q) 1 (meaning188 q) (meaning367 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause824 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 367 = true := counterClause824 (baseVal q)

theorem counterClause825 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (367)) (countLit q [187]) (countLit q [188]) (count367 q) 1 (meaning187 q) (meaning367 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause825 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 367 = true := counterClause825 (baseVal q)

theorem counterClause826 (q : Nat → Bool) : valuationOf q 190 = false ∨ valuationOf q 369 = true := by
  have hs : count369 q = (countLit q [189]) + (countLit q [190]) := List.countP_append (p := literal q) (l₁ := [189]) (l₂ := [190])
  have hm := merge_right (literal (valuationOf q) (190)) (literal (valuationOf q) (369)) (countLit q [189]) (countLit q [190]) (count369 q) 1 (meaning190 q) (meaning369 q) hs
  change valuationOf q 190 = false ∨ valuationOf q 369 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause826 (q : Snake 81) (h : Conditions q) : valuation q 190 = false ∨ valuation q 369 = true := counterClause826 (baseVal q)

theorem counterClause827 (q : Nat → Bool) : valuationOf q 369 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_right (literal (valuationOf q) (369)) (literal (valuationOf q) (371)) (countLit q [187, 188]) (countLit q [189, 190]) (count371 q) 1 (meaning369 q) (meaning371 q) hs
  change valuationOf q 369 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause827 (q : Snake 81) (h : Conditions q) : valuation q 369 = false ∨ valuation q 371 = true := counterClause827 (baseVal q)

theorem counterClause828 (q : Nat → Bool) : valuationOf q 367 = false ∨ valuationOf q 371 = true := by
  have hs : count371 q = (countLit q [187, 188]) + (countLit q [189, 190]) := List.countP_append (p := literal q) (l₁ := [187, 188]) (l₂ := [189, 190])
  have hm := merge_left (literal (valuationOf q) (367)) (literal (valuationOf q) (371)) (countLit q [187, 188]) (countLit q [189, 190]) (count371 q) 1 (meaning367 q) (meaning371 q) hs
  change valuationOf q 367 = false ∨ valuationOf q 371 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause828 (q : Snake 81) (h : Conditions q) : valuation q 367 = false ∨ valuation q 371 = true := counterClause828 (baseVal q)

theorem counterClause829 (q : Nat → Bool) : valuationOf q 371 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (371)) (literal (valuationOf q) (373)) (countLit q [184, 185, 186]) (countLit q [187, 188, 189, 190]) (count373 q) 1 (meaning371 q) (meaning373 q) hs
  change valuationOf q 371 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause829 (q : Snake 81) (h : Conditions q) : valuation q 371 = false ∨ valuation q 373 = true := counterClause829 (baseVal q)

theorem counterClause830 (q : Nat → Bool) : valuationOf q 365 = false ∨ valuationOf q 373 = true := by
  have hs : count373 q = (countLit q [184, 185, 186]) + (countLit q [187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [184, 185, 186]) (l₂ := [187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (365)) (literal (valuationOf q) (373)) (countLit q [184, 185, 186]) (countLit q [187, 188, 189, 190]) (count373 q) 1 (meaning365 q) (meaning373 q) hs
  change valuationOf q 365 = false ∨ valuationOf q 373 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause830 (q : Snake 81) (h : Conditions q) : valuation q 365 = false ∨ valuation q 373 = true := counterClause830 (baseVal q)

theorem counterClause831 (q : Nat → Bool) : valuationOf q 373 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190])
  have hm := merge_right (literal (valuationOf q) (373)) (literal (valuationOf q) (375)) (countLit q [177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190]) (count375 q) 1 (meaning373 q) (meaning375 q) hs
  change valuationOf q 373 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause831 (q : Snake 81) (h : Conditions q) : valuation q 373 = false ∨ valuation q 375 = true := counterClause831 (baseVal q)

theorem counterClause832 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 375 = true := by
  have hs : count375 q = (countLit q [177, 178, 179, 180, 181, 182, 183]) + (countLit q [184, 185, 186, 187, 188, 189, 190]) := List.countP_append (p := literal q) (l₁ := [177, 178, 179, 180, 181, 182, 183]) (l₂ := [184, 185, 186, 187, 188, 189, 190])
  have hm := merge_left (literal (valuationOf q) (361)) (literal (valuationOf q) (375)) (countLit q [177, 178, 179, 180, 181, 182, 183]) (countLit q [184, 185, 186, 187, 188, 189, 190]) (count375 q) 1 (meaning361 q) (meaning375 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 375 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause832 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 375 = true := counterClause832 (baseVal q)

theorem block25 (q : Snake 81) (h : Conditions q) : B112E158.Block25 (valuation q) :=
  ⟨clause801 q h, clause802 q h, clause803 q h, clause804 q h, clause805 q h, clause806 q h, clause807 q h, clause808 q h, clause809 q h, clause810 q h, clause811 q h, clause812 q h, clause813 q h, clause814 q h, clause815 q h, clause816 q h, clause817 q h, clause818 q h, clause819 q h, clause820 q h, clause821 q h, clause822 q h, clause823 q h, clause824 q h, clause825 q h, clause826 q h, clause827 q h, clause828 q h, clause829 q h, clause830 q h, clause831 q h, clause832 q h⟩

end
end Snake9.Regrowth.E112158
