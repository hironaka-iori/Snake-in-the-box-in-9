import E112096Semantics
import B112E096Inputs
namespace Snake9.Regrowth.E112096
noncomputable section
local instance blockDec17 (p : Prop) : Decidable p := Classical.propDecidable p
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedVariables false
theorem counterClause545 (q : Nat → Bool) : valuationOf q 347 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177])
  have hm := merge_right (literal (valuationOf q) (347)) (literal (valuationOf q) (349)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (count349 q) 1 (meaning347 q) (meaning349 q) hs
  change valuationOf q 347 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause545 (q : Snake 81) (h : Conditions q) : valuation q 347 = false ∨ valuation q 349 = true := counterClause545 (baseVal q)

theorem counterClause546 (q : Nat → Bool) : valuationOf q 348 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177])
  have hm := merge_right (literal (valuationOf q) (348)) (literal (valuationOf q) (350)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (count349 q) 2 (meaning348 q) (meaning350 q) hs
  change valuationOf q 348 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause546 (q : Snake 81) (h : Conditions q) : valuation q 348 = false ∨ valuation q 350 = true := counterClause546 (baseVal q)

theorem counterClause547 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 349 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177])
  have hm := merge_left (literal (valuationOf q) (291)) (literal (valuationOf q) (349)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (count349 q) 1 (meaning291 q) (meaning349 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 349 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause547 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 349 = true := counterClause547 (baseVal q)

theorem counterClause548 (q : Nat → Bool) : valuationOf q 291 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177])
  have hm := merge_two (literal (valuationOf q) (291)) (literal (valuationOf q) (347)) (literal (valuationOf q) (350)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (count349 q) 1 1 (meaning291 q) (meaning347 q) (meaning350 q) hs
  change valuationOf q 291 = false ∨ valuationOf q 347 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause548 (q : Snake 81) (h : Conditions q) : valuation q 291 = false ∨ valuation q 347 = false ∨ valuation q 350 = true := counterClause548 (baseVal q)

theorem counterClause549 (q : Nat → Bool) : valuationOf q 292 = false ∨ valuationOf q 350 = true := by
  have hs : count349 q = (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) + (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) := List.countP_append (p := literal q) (l₁ := [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (l₂ := [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177])
  have hm := merge_left (literal (valuationOf q) (292)) (literal (valuationOf q) (350)) (countLit q [119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147]) (countLit q [148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 177]) (count349 q) 2 (meaning292 q) (meaning350 q) hs
  change valuationOf q 292 = false ∨ valuationOf q 350 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause549 (q : Snake 81) (h : Conditions q) : valuation q 292 = false ∨ valuation q 350 = true := counterClause549 (baseVal q)

theorem counterClause550 (q : Nat → Bool) : valuationOf q 205 = false ∨ valuationOf q 397 = true := by
  have hs : count397 q = (countLit q [205]) + (countLit q [206]) := List.countP_append (p := literal q) (l₁ := [205]) (l₂ := [206])
  have hm := merge_left (literal (valuationOf q) (205)) (literal (valuationOf q) (397)) (countLit q [205]) (countLit q [206]) (count397 q) 1 (meaning205 q) (meaning397 q) hs
  change valuationOf q 205 = false ∨ valuationOf q 397 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause550 (q : Snake 81) (h : Conditions q) : valuation q 205 = false ∨ valuation q 397 = true := counterClause550 (baseVal q)

theorem counterClause551 (q : Nat → Bool) : valuationOf q 397 = false ∨ valuationOf q 399 = true := by
  have hs : count399 q = (countLit q [203, 204]) + (countLit q [205, 206]) := List.countP_append (p := literal q) (l₁ := [203, 204]) (l₂ := [205, 206])
  have hm := merge_right (literal (valuationOf q) (397)) (literal (valuationOf q) (399)) (countLit q [203, 204]) (countLit q [205, 206]) (count399 q) 1 (meaning397 q) (meaning399 q) hs
  change valuationOf q 397 = false ∨ valuationOf q 399 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause551 (q : Snake 81) (h : Conditions q) : valuation q 397 = false ∨ valuation q 399 = true := counterClause551 (baseVal q)

theorem counterClause552 (q : Nat → Bool) : valuationOf q 399 = false ∨ valuationOf q 401 = true := by
  have hs : count401 q = (countLit q [199, 200, 201, 202]) + (countLit q [203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [199, 200, 201, 202]) (l₂ := [203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (399)) (literal (valuationOf q) (401)) (countLit q [199, 200, 201, 202]) (countLit q [203, 204, 205, 206]) (count401 q) 1 (meaning399 q) (meaning401 q) hs
  change valuationOf q 399 = false ∨ valuationOf q 401 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause552 (q : Snake 81) (h : Conditions q) : valuation q 399 = false ∨ valuation q 401 = true := counterClause552 (baseVal q)

theorem counterClause553 (q : Nat → Bool) : valuationOf q 401 = false ∨ valuationOf q 403 = true := by
  have hs : count403 q = (countLit q [192, 193, 194, 195, 196, 197, 198]) + (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [192, 193, 194, 195, 196, 197, 198]) (l₂ := [199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (401)) (literal (valuationOf q) (403)) (countLit q [192, 193, 194, 195, 196, 197, 198]) (countLit q [199, 200, 201, 202, 203, 204, 205, 206]) (count403 q) 1 (meaning401 q) (meaning403 q) hs
  change valuationOf q 401 = false ∨ valuationOf q 403 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause553 (q : Snake 81) (h : Conditions q) : valuation q 401 = false ∨ valuation q 403 = true := counterClause553 (baseVal q)

theorem counterClause554 (q : Nat → Bool) : valuationOf q 403 = false ∨ valuationOf q 405 = true := by
  have hs : count405 q = (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) + (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) := List.countP_append (p := literal q) (l₁ := [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (l₂ := [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206])
  have hm := merge_right (literal (valuationOf q) (403)) (literal (valuationOf q) (405)) (countLit q [178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]) (countLit q [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206]) (count405 q) 1 (meaning403 q) (meaning405 q) hs
  change valuationOf q 403 = false ∨ valuationOf q 405 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause554 (q : Snake 81) (h : Conditions q) : valuation q 403 = false ∨ valuation q 405 = true := counterClause554 (baseVal q)

theorem counterClause555 (q : Nat → Bool) : valuationOf q 209 = false ∨ valuationOf q 407 = true := by
  have hs : count407 q = (countLit q [208]) + (countLit q [209]) := List.countP_append (p := literal q) (l₁ := [208]) (l₂ := [209])
  have hm := merge_right (literal (valuationOf q) (209)) (literal (valuationOf q) (407)) (countLit q [208]) (countLit q [209]) (count407 q) 1 (meaning209 q) (meaning407 q) hs
  change valuationOf q 209 = false ∨ valuationOf q 407 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause555 (q : Snake 81) (h : Conditions q) : valuation q 209 = false ∨ valuation q 407 = true := counterClause555 (baseVal q)

theorem counterClause556 (q : Nat → Bool) : valuationOf q 407 = false ∨ valuationOf q 409 = true := by
  have hs : count409 q = (countLit q [207]) + (countLit q [208, 209]) := List.countP_append (p := literal q) (l₁ := [207]) (l₂ := [208, 209])
  have hm := merge_right (literal (valuationOf q) (407)) (literal (valuationOf q) (409)) (countLit q [207]) (countLit q [208, 209]) (count409 q) 1 (meaning407 q) (meaning409 q) hs
  change valuationOf q 407 = false ∨ valuationOf q 409 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause556 (q : Snake 81) (h : Conditions q) : valuation q 407 = false ∨ valuation q 409 = true := counterClause556 (baseVal q)

theorem counterClause557 (q : Nat → Bool) : valuationOf q 212 = false ∨ valuationOf q 413 = true := by
  have hs : count413 q = (countLit q [212]) + (countLit q [213]) := List.countP_append (p := literal q) (l₁ := [212]) (l₂ := [213])
  have hm := merge_left (literal (valuationOf q) (212)) (literal (valuationOf q) (413)) (countLit q [212]) (countLit q [213]) (count413 q) 1 (meaning212 q) (meaning413 q) hs
  change valuationOf q 212 = false ∨ valuationOf q 413 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause557 (q : Snake 81) (h : Conditions q) : valuation q 212 = false ∨ valuation q 413 = true := counterClause557 (baseVal q)

theorem counterClause558 (q : Nat → Bool) : valuationOf q 413 = false ∨ valuationOf q 415 = true := by
  have hs : count415 q = (countLit q [210, 211]) + (countLit q [212, 213]) := List.countP_append (p := literal q) (l₁ := [210, 211]) (l₂ := [212, 213])
  have hm := merge_right (literal (valuationOf q) (413)) (literal (valuationOf q) (415)) (countLit q [210, 211]) (countLit q [212, 213]) (count415 q) 1 (meaning413 q) (meaning415 q) hs
  change valuationOf q 413 = false ∨ valuationOf q 415 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause558 (q : Snake 81) (h : Conditions q) : valuation q 413 = false ∨ valuation q 415 = true := counterClause558 (baseVal q)

theorem counterClause559 (q : Nat → Bool) : valuationOf q 415 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_right (literal (valuationOf q) (415)) (literal (valuationOf q) (417)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count417 q) 1 (meaning415 q) (meaning417 q) hs
  change valuationOf q 415 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause559 (q : Snake 81) (h : Conditions q) : valuation q 415 = false ∨ valuation q 417 = true := counterClause559 (baseVal q)

theorem counterClause560 (q : Nat → Bool) : valuationOf q 409 = false ∨ valuationOf q 417 = true := by
  have hs : count417 q = (countLit q [207, 208, 209]) + (countLit q [210, 211, 212, 213]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209]) (l₂ := [210, 211, 212, 213])
  have hm := merge_left (literal (valuationOf q) (409)) (literal (valuationOf q) (417)) (countLit q [207, 208, 209]) (countLit q [210, 211, 212, 213]) (count417 q) 1 (meaning409 q) (meaning417 q) hs
  change valuationOf q 409 = false ∨ valuationOf q 417 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause560 (q : Snake 81) (h : Conditions q) : valuation q 409 = false ∨ valuation q 417 = true := counterClause560 (baseVal q)

theorem counterClause561 (q : Nat → Bool) : valuationOf q 215 = false ∨ valuationOf q 419 = true := by
  have hs : count419 q = (countLit q [214]) + (countLit q [215]) := List.countP_append (p := literal q) (l₁ := [214]) (l₂ := [215])
  have hm := merge_right (literal (valuationOf q) (215)) (literal (valuationOf q) (419)) (countLit q [214]) (countLit q [215]) (count419 q) 1 (meaning215 q) (meaning419 q) hs
  change valuationOf q 215 = false ∨ valuationOf q 419 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause561 (q : Snake 81) (h : Conditions q) : valuation q 215 = false ∨ valuation q 419 = true := counterClause561 (baseVal q)

theorem counterClause562 (q : Nat → Bool) : valuationOf q 419 = false ∨ valuationOf q 423 = true := by
  have hs : count423 q = (countLit q [214, 215]) + (countLit q [216, 217]) := List.countP_append (p := literal q) (l₁ := [214, 215]) (l₂ := [216, 217])
  have hm := merge_left (literal (valuationOf q) (419)) (literal (valuationOf q) (423)) (countLit q [214, 215]) (countLit q [216, 217]) (count423 q) 1 (meaning419 q) (meaning423 q) hs
  change valuationOf q 419 = false ∨ valuationOf q 423 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause562 (q : Snake 81) (h : Conditions q) : valuation q 419 = false ∨ valuation q 423 = true := counterClause562 (baseVal q)

theorem counterClause563 (q : Nat → Bool) : valuationOf q 221 = false ∨ valuationOf q 427 = true := by
  have hs : count427 q = (countLit q [220]) + (countLit q [221]) := List.countP_append (p := literal q) (l₁ := [220]) (l₂ := [221])
  have hm := merge_right (literal (valuationOf q) (221)) (literal (valuationOf q) (427)) (countLit q [220]) (countLit q [221]) (count427 q) 1 (meaning221 q) (meaning427 q) hs
  change valuationOf q 221 = false ∨ valuationOf q 427 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause563 (q : Snake 81) (h : Conditions q) : valuation q 221 = false ∨ valuation q 427 = true := counterClause563 (baseVal q)

theorem counterClause564 (q : Nat → Bool) : valuationOf q 427 = false ∨ valuationOf q 429 = true := by
  have hs : count429 q = (countLit q [218, 219]) + (countLit q [220, 221]) := List.countP_append (p := literal q) (l₁ := [218, 219]) (l₂ := [220, 221])
  have hm := merge_right (literal (valuationOf q) (427)) (literal (valuationOf q) (429)) (countLit q [218, 219]) (countLit q [220, 221]) (count429 q) 1 (meaning427 q) (meaning429 q) hs
  change valuationOf q 427 = false ∨ valuationOf q 429 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause564 (q : Snake 81) (h : Conditions q) : valuation q 427 = false ∨ valuation q 429 = true := counterClause564 (baseVal q)

theorem counterClause565 (q : Nat → Bool) : valuationOf q 429 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (429)) (literal (valuationOf q) (431)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 (meaning429 q) (meaning431 q) hs
  change valuationOf q 429 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause565 (q : Snake 81) (h : Conditions q) : valuation q 429 = false ∨ valuation q 431 = true := counterClause565 (baseVal q)

theorem counterClause566 (q : Nat → Bool) : valuationOf q 423 = false ∨ valuationOf q 431 = true := by
  have hs : count431 q = (countLit q [214, 215, 216, 217]) + (countLit q [218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [214, 215, 216, 217]) (l₂ := [218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (423)) (literal (valuationOf q) (431)) (countLit q [214, 215, 216, 217]) (countLit q [218, 219, 220, 221]) (count431 q) 1 (meaning423 q) (meaning431 q) hs
  change valuationOf q 423 = false ∨ valuationOf q 431 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause566 (q : Snake 81) (h : Conditions q) : valuation q 423 = false ∨ valuation q 431 = true := counterClause566 (baseVal q)

theorem counterClause567 (q : Nat → Bool) : valuationOf q 431 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_right (literal (valuationOf q) (431)) (literal (valuationOf q) (433)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 (meaning431 q) (meaning433 q) hs
  change valuationOf q 431 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause567 (q : Snake 81) (h : Conditions q) : valuation q 431 = false ∨ valuation q 433 = true := counterClause567 (baseVal q)

theorem counterClause568 (q : Nat → Bool) : valuationOf q 417 = false ∨ valuationOf q 433 = true := by
  have hs : count433 q = (countLit q [207, 208, 209, 210, 211, 212, 213]) + (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) := List.countP_append (p := literal q) (l₁ := [207, 208, 209, 210, 211, 212, 213]) (l₂ := [214, 215, 216, 217, 218, 219, 220, 221])
  have hm := merge_left (literal (valuationOf q) (417)) (literal (valuationOf q) (433)) (countLit q [207, 208, 209, 210, 211, 212, 213]) (countLit q [214, 215, 216, 217, 218, 219, 220, 221]) (count433 q) 1 (meaning417 q) (meaning433 q) hs
  change valuationOf q 417 = false ∨ valuationOf q 433 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause568 (q : Snake 81) (h : Conditions q) : valuation q 417 = false ∨ valuation q 433 = true := counterClause568 (baseVal q)

theorem counterClause569 (q : Nat → Bool) : valuationOf q 226 = false ∨ valuationOf q 439 = true := by
  have hs : count439 q = (countLit q [225]) + (countLit q [226]) := List.countP_append (p := literal q) (l₁ := [225]) (l₂ := [226])
  have hm := merge_right (literal (valuationOf q) (226)) (literal (valuationOf q) (439)) (countLit q [225]) (countLit q [226]) (count439 q) 1 (meaning226 q) (meaning439 q) hs
  change valuationOf q 226 = false ∨ valuationOf q 439 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause569 (q : Snake 81) (h : Conditions q) : valuation q 226 = false ∨ valuation q 439 = true := counterClause569 (baseVal q)

theorem counterClause570 (q : Nat → Bool) : valuationOf q 439 = false ∨ valuationOf q 443 = true := by
  have hs : count443 q = (countLit q [225, 226]) + (countLit q [227, 228]) := List.countP_append (p := literal q) (l₁ := [225, 226]) (l₂ := [227, 228])
  have hm := merge_left (literal (valuationOf q) (439)) (literal (valuationOf q) (443)) (countLit q [225, 226]) (countLit q [227, 228]) (count443 q) 1 (meaning439 q) (meaning443 q) hs
  change valuationOf q 439 = false ∨ valuationOf q 443 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause570 (q : Snake 81) (h : Conditions q) : valuation q 439 = false ∨ valuation q 443 = true := counterClause570 (baseVal q)

theorem counterClause571 (q : Nat → Bool) : valuationOf q 443 = false ∨ valuationOf q 445 = true := by
  have hs : count445 q = (countLit q [222, 223, 224]) + (countLit q [225, 226, 227, 228]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224]) (l₂ := [225, 226, 227, 228])
  have hm := merge_right (literal (valuationOf q) (443)) (literal (valuationOf q) (445)) (countLit q [222, 223, 224]) (countLit q [225, 226, 227, 228]) (count445 q) 1 (meaning443 q) (meaning445 q) hs
  change valuationOf q 443 = false ∨ valuationOf q 445 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause571 (q : Snake 81) (h : Conditions q) : valuation q 443 = false ∨ valuation q 445 = true := counterClause571 (baseVal q)

theorem counterClause572 (q : Nat → Bool) : valuationOf q 233 = false ∨ valuationOf q 453 = true := by
  have hs : count453 q = (countLit q [233]) + (countLit q [234]) := List.countP_append (p := literal q) (l₁ := [233]) (l₂ := [234])
  have hm := merge_left (literal (valuationOf q) (233)) (literal (valuationOf q) (453)) (countLit q [233]) (countLit q [234]) (count453 q) 1 (meaning233 q) (meaning453 q) hs
  change valuationOf q 233 = false ∨ valuationOf q 453 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause572 (q : Snake 81) (h : Conditions q) : valuation q 233 = false ∨ valuation q 453 = true := counterClause572 (baseVal q)

theorem counterClause573 (q : Nat → Bool) : valuationOf q 453 = false ∨ valuationOf q 457 = true := by
  have hs : count457 q = (countLit q [233, 234]) + (countLit q [235, 236]) := List.countP_append (p := literal q) (l₁ := [233, 234]) (l₂ := [235, 236])
  have hm := merge_left (literal (valuationOf q) (453)) (literal (valuationOf q) (457)) (countLit q [233, 234]) (countLit q [235, 236]) (count457 q) 1 (meaning453 q) (meaning457 q) hs
  change valuationOf q 453 = false ∨ valuationOf q 457 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause573 (q : Snake 81) (h : Conditions q) : valuation q 453 = false ∨ valuation q 457 = true := counterClause573 (baseVal q)

theorem counterClause574 (q : Nat → Bool) : valuationOf q 457 = false ∨ valuationOf q 459 = true := by
  have hs : count459 q = (countLit q [229, 230, 231, 232]) + (countLit q [233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [229, 230, 231, 232]) (l₂ := [233, 234, 235, 236])
  have hm := merge_right (literal (valuationOf q) (457)) (literal (valuationOf q) (459)) (countLit q [229, 230, 231, 232]) (countLit q [233, 234, 235, 236]) (count459 q) 1 (meaning457 q) (meaning459 q) hs
  change valuationOf q 457 = false ∨ valuationOf q 459 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause574 (q : Snake 81) (h : Conditions q) : valuation q 457 = false ∨ valuation q 459 = true := counterClause574 (baseVal q)

theorem counterClause575 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 461 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_left (literal (valuationOf q) (445)) (literal (valuationOf q) (461)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 1 (meaning445 q) (meaning461 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 461 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause575 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 461 = true := counterClause575 (baseVal q)

theorem counterClause576 (q : Nat → Bool) : valuationOf q 445 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true := by
  have hs : count461 q = (countLit q [222, 223, 224, 225, 226, 227, 228]) + (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) := List.countP_append (p := literal q) (l₁ := [222, 223, 224, 225, 226, 227, 228]) (l₂ := [229, 230, 231, 232, 233, 234, 235, 236])
  have hm := merge_two (literal (valuationOf q) (445)) (literal (valuationOf q) (459)) (literal (valuationOf q) (462)) (countLit q [222, 223, 224, 225, 226, 227, 228]) (countLit q [229, 230, 231, 232, 233, 234, 235, 236]) (count461 q) 1 1 (meaning445 q) (meaning459 q) (meaning462 q) hs
  change valuationOf q 445 = false ∨ valuationOf q 459 = false ∨ valuationOf q 462 = true at hm
  simpa only [Bool.not_eq_false] using hm

theorem clause576 (q : Snake 81) (h : Conditions q) : valuation q 445 = false ∨ valuation q 459 = false ∨ valuation q 462 = true := counterClause576 (baseVal q)

theorem block17 (q : Snake 81) (h : Conditions q) : B112E096.Block17 (valuation q) :=
  ⟨clause545 q h, clause546 q h, clause547 q h, clause548 q h, clause549 q h, clause550 q h, clause551 q h, clause552 q h, clause553 q h, clause554 q h, clause555 q h, clause556 q h, clause557 q h, clause558 q h, clause559 q h, clause560 q h, clause561 q h, clause562 q h, clause563 q h, clause564 q h, clause565 q h, clause566 q h, clause567 q h, clause568 q h, clause569 q h, clause570 q h, clause571 q h, clause572 q h, clause573 q h, clause574 q h, clause575 q h, clause576 q h⟩

end
end Snake9.Regrowth.E112096
