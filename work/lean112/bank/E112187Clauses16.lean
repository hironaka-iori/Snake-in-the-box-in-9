import E112187Semantics
import B112E187Inputs
namespace Snake9.Regrowth.E112187
noncomputable section
local instance blockDec16 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause513 (q : Nat → Bool) : valuationOf q 175 = false ∨ valuationOf q 341 = true := by
  have hs : count341 q = (countLit q [175]) + (countLit q [176]) := List.countP_append (p := literal q) (l₁ := [175]) (l₂ := [176])
  have hm := merge_left (literal (valuationOf q) (175)) (literal (valuationOf q) (341)) (countLit q [175]) (countLit q [176]) (count341 q) 1 (meaning175 q) (meaning341 q) hs
  change valuationOf q 175 = false ∨ valuationOf q 341 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause513 (q : Snake 81) (h : Conditions q) : valuation q 175 = false ∨ valuation q 341 = true := counterClause513 (baseVal q)

theorem counterClause514 (q : Nat → Bool) : valuationOf q 178 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_right (literal (valuationOf q) (178)) (literal (valuationOf q) (343)) (countLit q [177]) (countLit q [178]) (count343 q) 1 (meaning178 q) (meaning343 q) hs
  change valuationOf q 178 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause514 (q : Snake 81) (h : Conditions q) : valuation q 178 = false ∨ valuation q 343 = true := counterClause514 (baseVal q)

theorem counterClause515 (q : Nat → Bool) : valuationOf q 177 = false ∨ valuationOf q 343 = true := by
  have hs : count343 q = (countLit q [177]) + (countLit q [178]) := List.countP_append (p := literal q) (l₁ := [177]) (l₂ := [178])
  have hm := merge_left (literal (valuationOf q) (177)) (literal (valuationOf q) (343)) (countLit q [177]) (countLit q [178]) (count343 q) 1 (meaning177 q) (meaning343 q) hs
  change valuationOf q 177 = false ∨ valuationOf q 343 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause515 (q : Snake 81) (h : Conditions q) : valuation q 177 = false ∨ valuation q 343 = true := counterClause515 (baseVal q)

theorem counterClause516 (q : Nat → Bool) : valuationOf q 343 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_right (literal (valuationOf q) (343)) (literal (valuationOf q) (345)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 (meaning343 q) (meaning345 q) hs
  change valuationOf q 343 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause516 (q : Snake 81) (h : Conditions q) : valuation q 343 = false ∨ valuation q 345 = true := counterClause516 (baseVal q)

theorem counterClause517 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 345 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_left (literal (valuationOf q) (341)) (literal (valuationOf q) (345)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 (meaning341 q) (meaning345 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 345 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause517 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 345 = true := counterClause517 (baseVal q)

theorem counterClause518 (q : Nat → Bool) : valuationOf q 341 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true := by
  have hs : count345 q = (countLit q [175, 176]) + (countLit q [177, 178]) := List.countP_append (p := literal q) (l₁ := [175, 176]) (l₂ := [177, 178])
  have hm := merge_two (literal (valuationOf q) (341)) (literal (valuationOf q) (343)) (literal (valuationOf q) (346)) (countLit q [175, 176]) (countLit q [177, 178]) (count345 q) 1 1 (meaning341 q) (meaning343 q) (meaning346 q) hs
  change valuationOf q 341 = false ∨ valuationOf q 343 = false ∨ valuationOf q 346 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause518 (q : Snake 81) (h : Conditions q) : valuation q 341 = false ∨ valuation q 343 = false ∨ valuation q 346 = true := counterClause518 (baseVal q)

theorem counterClause519 (q : Nat → Bool) : valuationOf q 345 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (345)) (literal (valuationOf q) (347)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning345 q) (meaning347 q) hs
  change valuationOf q 345 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause519 (q : Snake 81) (h : Conditions q) : valuation q 345 = false ∨ valuation q 347 = true := counterClause519 (baseVal q)

theorem counterClause520 (q : Nat → Bool) : valuationOf q 346 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (346)) (literal (valuationOf q) (348)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 2 (meaning346 q) (meaning348 q) hs
  change valuationOf q 346 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause520 (q : Snake 81) (h : Conditions q) : valuation q 346 = false ∨ valuation q 348 = true := counterClause520 (baseVal q)

theorem counterClause521 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 347 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (339)) (literal (valuationOf q) (347)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 (meaning339 q) (meaning347 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 347 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause521 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 347 = true := counterClause521 (baseVal q)

theorem counterClause522 (q : Nat → Bool) : valuationOf q 339 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true := by
  have hs : count347 q = (countLit q [171, 172, 173, 174]) + (countLit q [175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [171, 172, 173, 174]) (l₂ := [175, 176, 177, 178])
  have hm := merge_two (literal (valuationOf q) (339)) (literal (valuationOf q) (345)) (literal (valuationOf q) (348)) (countLit q [171, 172, 173, 174]) (countLit q [175, 176, 177, 178]) (count347 q) 1 1 (meaning339 q) (meaning345 q) (meaning348 q) hs
  change valuationOf q 339 = false ∨ valuationOf q 345 = false ∨ valuationOf q 348 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause522 (q : Snake 81) (h : Conditions q) : valuation q 339 = false ∨ valuation q 345 = false ∨ valuation q 348 = true := counterClause522 (baseVal q)

theorem counterClause523 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause523 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause523 (baseVal q)

theorem counterClause524 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (348)) (literal (valuationOf q) (350)) (countLit q [164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (count349 q) 2 (meaning348 q) (meaning350 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause524 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 350 = true := counterClause524 (baseVal q)

theorem counterClause525 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (333)) (literal (valuationOf q) (349)) (countLit q [164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 (meaning333 q) (meaning349 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause525 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 349 = true := counterClause525 (baseVal q)

theorem counterClause526 (q : Nat → Bool) : valuationOf q 333 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_two (literal (valuationOf q) (333)) (literal (valuationOf q) (347)) (literal (valuationOf q) (350)) (countLit q [164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (count349 q) 1 1 (meaning333 q) (meaning347 q) (meaning350 q) hs
  change valuationOf q 333 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause526 (q : Snake 81) (h : Conditions q) : valuation q 333 = false ∨ valuation q 347 = false ∨ valuation q 350 = true := counterClause526 (baseVal q)

theorem counterClause527 (q : Nat → Bool) : valuationOf q 334 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [164, 165, 166, 167, 168, 169, 170]) + (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [164, 165, 166, 167, 168, 169, 170]) (l₂ := [171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (334)) (literal (valuationOf q) (350)) (countLit q [164, 165, 166, 167, 168, 169, 170]) (countLit q [171, 172, 173, 174, 175, 176, 177, 178]) (count349 q) 2 (meaning334 q) (meaning350 q) hs
  change valuationOf q 334 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause527 (q : Snake 81) (h : Conditions q) : valuation q 334 = false ∨ valuation q 350 = true := counterClause527 (baseVal q)

theorem counterClause528 (q : Nat → Bool) : valuationOf q 349 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (349)) (literal (valuationOf q) (351)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count351 q) 1 (meaning349 q) (meaning351 q) hs
  change valuationOf q 349 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause528 (q : Snake 81) (h : Conditions q) : valuation q 349 = false ∨ valuation q 351 = true := counterClause528 (baseVal q)

theorem counterClause529 (q : Nat → Bool) : valuationOf q 350 = false ∨ valuationOf q 352 = true := by
  have hs : count351 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (350)) (literal (valuationOf q) (352)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count351 q) 2 (meaning350 q) (meaning352 q) hs
  change valuationOf q 350 = false ∨ valuationOf q 352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause529 (q : Snake 81) (h : Conditions q) : valuation q 350 = false ∨ valuation q 352 = true := counterClause529 (baseVal q)

theorem counterClause530 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 351 = true := by
  have hs : count351 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (321)) (literal (valuationOf q) (351)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count351 q) 1 (meaning321 q) (meaning351 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 351 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause530 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 351 = true := counterClause530 (baseVal q)

theorem counterClause531 (q : Nat → Bool) : valuationOf q 321 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true := by
  have hs : count351 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_two (literal (valuationOf q) (321)) (literal (valuationOf q) (349)) (literal (valuationOf q) (352)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count351 q) 1 1 (meaning321 q) (meaning349 q) (meaning352 q) hs
  change valuationOf q 321 = false ∨ valuationOf q 349 = false ∨ valuationOf q 352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause531 (q : Snake 81) (h : Conditions q) : valuation q 321 = false ∨ valuation q 349 = false ∨ valuation q 352 = true := counterClause531 (baseVal q)

theorem counterClause532 (q : Nat → Bool) : valuationOf q 322 = false ∨ valuationOf q 352 = true := by
  have hs : count351 q = (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) + (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (l₂ := [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (322)) (literal (valuationOf q) (352)) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163]) (countLit q [164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count351 q) 2 (meaning322 q) (meaning352 q) hs
  change valuationOf q 322 = false ∨ valuationOf q 352 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause532 (q : Snake 81) (h : Conditions q) : valuation q 322 = false ∨ valuation q 352 = true := counterClause532 (baseVal q)

theorem counterClause533 (q : Nat → Bool) : valuationOf q 351 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (351)) (literal (valuationOf q) (353)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count353 q) 1 (meaning351 q) (meaning353 q) hs
  change valuationOf q 351 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause533 (q : Snake 81) (h : Conditions q) : valuation q 351 = false ∨ valuation q 353 = true := counterClause533 (baseVal q)

theorem counterClause534 (q : Nat → Bool) : valuationOf q 352 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_right (literal (valuationOf q) (352)) (literal (valuationOf q) (354)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count353 q) 2 (meaning352 q) (meaning354 q) hs
  change valuationOf q 352 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause534 (q : Snake 81) (h : Conditions q) : valuation q 352 = false ∨ valuation q 354 = true := counterClause534 (baseVal q)

theorem counterClause535 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 353 = true := by
  have hs : count353 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (293)) (literal (valuationOf q) (353)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count353 q) 1 (meaning293 q) (meaning353 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 353 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause535 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 353 = true := counterClause535 (baseVal q)

theorem counterClause536 (q : Nat → Bool) : valuationOf q 293 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_two (literal (valuationOf q) (293)) (literal (valuationOf q) (351)) (literal (valuationOf q) (354)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count353 q) 1 1 (meaning293 q) (meaning351 q) (meaning354 q) hs
  change valuationOf q 293 = false ∨ valuationOf q 351 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause536 (q : Snake 81) (h : Conditions q) : valuation q 293 = false ∨ valuation q 351 = false ∨ valuation q 354 = true := counterClause536 (baseVal q)

theorem counterClause537 (q : Nat → Bool) : valuationOf q 294 = false ∨ valuationOf q 354 = true := by
  have hs : count353 q = (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) + (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) := List.countP_append (p := literal q) (l₁ := [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (l₂ := [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178])
  have hm := merge_left (literal (valuationOf q) (294)) (literal (valuationOf q) (354)) (countLit q [120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148]) (countLit q [149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178]) (count353 q) 2 (meaning294 q) (meaning354 q) hs
  change valuationOf q 294 = false ∨ valuationOf q 354 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause537 (q : Snake 81) (h : Conditions q) : valuation q 294 = false ∨ valuation q 354 = true := counterClause537 (baseVal q)

theorem counterClause538 (q : Nat → Bool) : valuationOf q 179 = false ∨ valuationOf q 357 = true := by
  have hs : count357 q = (countLit q [179]) + (countLit q [180, 181]) := List.countP_append (p := literal q) (l₁ := [179]) (l₂ := [180, 181])
  have hm := merge_left (literal (valuationOf q) (179)) (literal (valuationOf q) (357)) (countLit q [179]) (countLit q [180, 181]) (count357 q) 1 (meaning179 q) (meaning357 q) hs
  change valuationOf q 179 = false ∨ valuationOf q 357 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause538 (q : Snake 81) (h : Conditions q) : valuation q 179 = false ∨ valuation q 357 = true := counterClause538 (baseVal q)

theorem counterClause539 (q : Nat → Bool) : valuationOf q 184 = false ∨ valuationOf q 361 = true := by
  have hs : count361 q = (countLit q [184]) + (countLit q [185]) := List.countP_append (p := literal q) (l₁ := [184]) (l₂ := [185])
  have hm := merge_left (literal (valuationOf q) (184)) (literal (valuationOf q) (361)) (countLit q [184]) (countLit q [185]) (count361 q) 1 (meaning184 q) (meaning361 q) hs
  change valuationOf q 184 = false ∨ valuationOf q 361 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause539 (q : Snake 81) (h : Conditions q) : valuation q 184 = false ∨ valuation q 361 = true := counterClause539 (baseVal q)

theorem counterClause540 (q : Nat → Bool) : valuationOf q 361 = false ∨ valuationOf q 363 = true := by
  have hs : count363 q = (countLit q [182, 183]) + (countLit q [184, 185]) := List.countP_append (p := literal q) (l₁ := [182, 183]) (l₂ := [184, 185])
  have hm := merge_right (literal (valuationOf q) (361)) (literal (valuationOf q) (363)) (countLit q [182, 183]) (countLit q [184, 185]) (count363 q) 1 (meaning361 q) (meaning363 q) hs
  change valuationOf q 361 = false ∨ valuationOf q 363 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause540 (q : Snake 81) (h : Conditions q) : valuation q 361 = false ∨ valuation q 363 = true := counterClause540 (baseVal q)

theorem counterClause541 (q : Nat → Bool) : valuationOf q 363 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_right (literal (valuationOf q) (363)) (literal (valuationOf q) (365)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count365 q) 1 (meaning363 q) (meaning365 q) hs
  change valuationOf q 363 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause541 (q : Snake 81) (h : Conditions q) : valuation q 363 = false ∨ valuation q 365 = true := counterClause541 (baseVal q)

theorem counterClause542 (q : Nat → Bool) : valuationOf q 357 = false ∨ valuationOf q 365 = true := by
  have hs : count365 q = (countLit q [179, 180, 181]) + (countLit q [182, 183, 184, 185]) := List.countP_append (p := literal q) (l₁ := [179, 180, 181]) (l₂ := [182, 183, 184, 185])
  have hm := merge_left (literal (valuationOf q) (357)) (literal (valuationOf q) (365)) (countLit q [179, 180, 181]) (countLit q [182, 183, 184, 185]) (count365 q) 1 (meaning357 q) (meaning365 q) hs
  change valuationOf q 357 = false ∨ valuationOf q 365 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause542 (q : Snake 81) (h : Conditions q) : valuation q 357 = false ∨ valuation q 365 = true := counterClause542 (baseVal q)

theorem counterClause543 (q : Nat → Bool) : valuationOf q 188 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_right (literal (valuationOf q) (188)) (literal (valuationOf q) (367)) (countLit q [187]) (countLit q [188]) (count367 q) 1 (meaning188 q) (meaning367 q) hs
  change valuationOf q 188 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause543 (q : Snake 81) (h : Conditions q) : valuation q 188 = false ∨ valuation q 367 = true := counterClause543 (baseVal q)

theorem counterClause544 (q : Nat → Bool) : valuationOf q 187 = false ∨ valuationOf q 367 = true := by
  have hs : count367 q = (countLit q [187]) + (countLit q [188]) := List.countP_append (p := literal q) (l₁ := [187]) (l₂ := [188])
  have hm := merge_left (literal (valuationOf q) (187)) (literal (valuationOf q) (367)) (countLit q [187]) (countLit q [188]) (count367 q) 1 (meaning187 q) (meaning367 q) hs
  change valuationOf q 187 = false ∨ valuationOf q 367 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause544 (q : Snake 81) (h : Conditions q) : valuation q 187 = false ∨ valuation q 367 = true := counterClause544 (baseVal q)

theorem block16 (q : Snake 81) (h : Conditions q) : B112E187.Block16 (valuation q) :=
  ⟨clause513 q h, clause514 q h, clause515 q h, clause516 q h, clause517 q h, clause518 q h, clause519 q h, clause520 q h, clause521 q h, clause522 q h, clause523 q h, clause524 q h, clause525 q h, clause526 q h, clause527 q h, clause528 q h, clause529 q h, clause530 q h, clause531 q h, clause532 q h, clause533 q h, clause534 q h, clause535 q h, clause536 q h, clause537 q h, clause538 q h, clause539 q h, clause540 q h, clause541 q h, clause542 q h, clause543 q h, clause544 q h⟩

end
end Snake9.Regrowth.E112187
